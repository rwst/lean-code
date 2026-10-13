#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code. Released under CC0 1.0 Universal.
"""Harvest and triage the forward citations of a work from OpenAlex.

Written for L0 gate item (vi) of ``plans/plan-1061.html``: the [Bug12] Ch. 10
forward-citation sweep (Bugeaud, *Distribution Modulo One and Diophantine
Approximation*, CUP 2012 -- the chapter is the book's open-problem list, so its
citers are the last place a post-2012 solution of Problem 10.61 could hide).

OpenAlex has no chapter granularity for a monograph, so this fetches every citer
of the book and ranks them, rather than pretending to filter by chapter.

Output (in ``--out``, default ``~/math/scholar/openalex-<slug>/``):

  meta.json    provenance: seeds, filters, request log, counts, UTC timestamps
  works.jsonl  one JSON record per citer, verbatim from OpenAlex plus a
               reconstructed ``abstract`` and the computed triage fields
  triage.tsv   score-sorted table for reading
  triage.md    the same as a shortlist, tiered, ready to paste into an L0 note

Politeness: OpenAlex asks for a mailto in the query string to join the polite
pool.  It is NOT filled in automatically -- pass ``--mailto`` yourself if you
want it, since that publishes the address to a third-party service.

Examples
--------
    # the default: Bugeaud 2012, into ~/math/scholar/openalex-bug12/
    ./scripts/openalex_citers.py

    # mark citers that ALSO cite [BM86], Rauzy 1970, [MF70] or [MF68].
    # (Verified IDs.  [MF67] itself is NOT in OpenAlex; as of 2026-08-23 the
    # intersection with the Bug12 citers is empty for all four -- OpenAlex's
    # reference extraction for pre-1990 French journals is thin, so read an
    # empty co-citation column as "no signal", not as "no overlap".)
    ./scripts/openalex_citers.py --cocite 10.24033/bsmf.2058 --cocite W2585331639 \
                                 --cocite W4206572391 --cocite W4233927312

    # re-triage an existing harvest without hitting the network
    ./scripts/openalex_citers.py --offline

    # pull the open-access PDFs of the 15 best-scoring citers
    ./scripts/openalex_citers.py --offline --download-top 15
"""

from __future__ import annotations

import argparse
import json
import os
import re
import sys
import time
import urllib.error
import urllib.parse
import urllib.request
from datetime import datetime, timezone
from pathlib import Path

API = "https://api.openalex.org"
UA = "openalex_citers.py/1.0 (research literature audit; https://openalex.org)"

# Default seed: Bugeaud, Distribution Modulo One and Diophantine Approximation,
# CUP 2012 = [Bug12].  The other two OpenAlex records under that title are a
# Bulletin AMS book review and an arXiv listing, both with ~0 citers.
DEFAULT_SEEDS = ["10.1017/cbo9781139017732"]

SELECT = ",".join([
    "id", "doi", "ids", "display_name", "publication_year", "publication_date",
    "type", "language", "cited_by_count", "authorships", "primary_location",
    "best_oa_location", "open_access", "abstract_inverted_index",
    "referenced_works", "topics", "keywords",
])

# ---------------------------------------------------------------------------
# Triage lexicon.  Weights are deliberately coarse: the point is to sort 200
# titles into "read", "skim", "noise", not to be a classifier.
# ---------------------------------------------------------------------------

LEXICON: list[tuple[int, str, str]] = [
    # (weight, tag, regex).  Matched case-insensitively; a hit in the TITLE
    # counts double, because 1/3 of OpenAlex records carry no abstract and the
    # title is the only text guaranteed to be there.
    (5, "mfname",   r"Mend[eè]s[- ]?France"),
    (5, "solves",   r"\b(answer(?:s|ing)?|solv(?:e|es|ing)|settl(?:e|es|ing)|resolv(?:e|es|ing))\b"
                    r"[^.]{0,60}\b(question|problem|conjecture)\b"),
    (5, "bugeaud",  r"\b(question|problem|conjecture)s?\b[^.]{0,40}\bBugeaud\b"),
    (4, "bmname",   r"Bertrand[- ]Mathis"),
    (4, "openprob", r"\bopen (problem|question)s?\b"),
    (4, "pisot",    r"\bPisot\b"),
    (3, "salem",    r"\bSalem number"),
    (3, "beta",     r"(β|beta)[- ](expansion|shift|numeration|transformation)|\bnumeration system"),
    (3, "normset",  r"\bnormal set"),
    (3, "udmod1",   r"\b(uniform(?:ly)? distribut|equidistribut)"),
    (3, "modone",   r"\b(modulo one|mod(?:ulo)? 1)\b"),
    (3, "fracpart", r"\b(fractional part|distance to the nearest integer)"),
    (3, "lacunary", r"\blacunar|\bgeometric progression"),
    (3, "threehalf",r"\(3/2\)|\bthree.halves\b"),
    (3, "mahler",   r"\bMahler\b|\bZ-number"),
    (3, "selfsim",  r"\bself-(similar|conformal|affine)\b"),
    (3, "fourier",  r"\bFourier (decay|dimension|transform)|\bRajchman\b"),
    (2, "cantor",   r"\bCantor set|\bmiddle-thirds?\b|\bfractal\b|\bHausdorff dimension\b"),
    (2, "normnum",  r"\bnormal number|\bnormality\b|\babsolutely normal\b|\bpointwise normal"),
    (2, "digits",   r"\bdigit(s|al)?\b|\bexpansion(s)? (of|in) (a )?(real|base)"),
    (2, "algint",   r"\balgebraic (integer|number)s?\b|\bconjugate(s)?\b"),
    (1, "diophant", r"\bDiophantine\b"),
    (1, "contfrac", r"\bcontinued fraction"),
    (1, "transc",   r"\btranscend"),
    (1, "irrat",    r"\birrationality (measure|exponent)\b"),
]

# Tags that, on their own, put a paper in the 10.61 circle rather than merely in
# the book's general orbit.  A tier-A/B verdict requires at least one.
CORE_TAGS = {"mfname", "bmname", "pisot", "salem", "beta", "normset", "udmod1",
             "modone", "fracpart", "lacunary", "threehalf", "mahler", "selfsim",
             "fourier"}


def utcnow() -> str:
    return datetime.now(timezone.utc).strftime("%Y-%m-%dT%H:%M:%SZ")


# ---------------------------------------------------------------------------
# HTTP
# ---------------------------------------------------------------------------

class Client:
    def __init__(self, mailto: str | None, sleep: float, log: list):
        self.mailto = mailto
        self.sleep = sleep
        self.log = log

    def get(self, path: str, params: dict) -> dict:
        p = dict(params)
        if self.mailto:
            p["mailto"] = self.mailto
        url = f"{API}{path}?{urllib.parse.urlencode(p, safe=':,|/')}"
        last = None
        for attempt in range(5):
            req = urllib.request.Request(url, headers={"User-Agent": UA,
                                                       "Accept": "application/json"})
            try:
                with urllib.request.urlopen(req, timeout=60) as r:
                    body = r.read().decode("utf-8")
                self.log.append({"url": url, "status": 200, "at": utcnow(),
                                 "bytes": len(body)})
                time.sleep(self.sleep)
                return json.loads(body)
            except urllib.error.HTTPError as e:
                last = f"HTTP {e.code}"
                self.log.append({"url": url, "status": e.code, "at": utcnow()})
                if e.code in (429, 500, 502, 503, 504):
                    time.sleep(2 ** attempt)
                    continue
                raise
            except (urllib.error.URLError, TimeoutError, OSError) as e:
                last = str(e)
                self.log.append({"url": url, "status": "error", "at": utcnow(),
                                 "error": str(e)})
                time.sleep(2 ** attempt)
        raise SystemExit(f"giving up on {url}: {last}")


def as_work_id(client: Client, ref: str) -> tuple[str, dict]:
    """Accept a bare OpenAlex ID, an OpenAlex URL, or a DOI; return (W-id, work)."""
    ref = ref.strip()
    m = re.search(r"(W\d+)", ref)
    if m:
        w = client.get(f"/works/{m.group(1)}", {"select": SELECT})
        return m.group(1), w
    doi = re.sub(r"^https?://(dx\.)?doi\.org/", "", ref, flags=re.I)
    d = client.get("/works", {"filter": f"doi:{doi}", "select": SELECT})
    if not d.get("results"):
        raise SystemExit(f"cannot resolve {ref!r} in OpenAlex")
    w = d["results"][0]
    return w["id"].rsplit("/", 1)[-1], w


# ---------------------------------------------------------------------------
# Harvest
# ---------------------------------------------------------------------------

def deinvert(idx: dict | None) -> str:
    """Rebuild an abstract from OpenAlex's inverted index."""
    if not idx:
        return ""
    pos: list[tuple[int, str]] = []
    for word, places in idx.items():
        for p in places:
            pos.append((p, word))
    pos.sort()
    return " ".join(w for _, w in pos)


def fetch_citers(client: Client, seed_ids: list[str], per_page: int) -> list[dict]:
    """All works citing ANY of seed_ids (OpenAlex ORs a pipe-joined filter)."""
    out: dict[str, dict] = {}
    cursor = "*"
    while cursor:
        d = client.get("/works", {
            "filter": "cites:" + "|".join(seed_ids),
            "select": SELECT,
            "per-page": str(per_page),
            "cursor": cursor,
        })
        for w in d.get("results", []):
            out[w["id"]] = w
        cursor = d.get("meta", {}).get("next_cursor")
        if not d.get("results"):
            break
    return list(out.values())


# ---------------------------------------------------------------------------
# Triage
# ---------------------------------------------------------------------------

def score(work: dict, cocite_ids: set[str]) -> dict:
    title = work.get("display_name") or ""
    rest = " ".join([
        work.get("abstract") or "",
        " ".join(t.get("display_name", "") for t in (work.get("topics") or [])),
        " ".join(k.get("display_name", "") for k in (work.get("keywords") or [])),
    ])
    hits, total = [], 0
    for weight, tag, rx in LEXICON:
        in_title = bool(re.search(rx, title, re.I))
        in_rest = bool(re.search(rx, rest, re.I))
        if in_title or in_rest:
            hits.append(tag.upper() if in_title else tag)
            total += 2 * weight if in_title else weight
    co = sorted({c for c in (work.get("referenced_works") or [])
                 if c.rsplit("/", 1)[-1] in cocite_ids})
    total += 6 * len(co)
    core = [h for h in hits if h.lower() in CORE_TAGS]
    if total >= 14 and core:
        tier = "A"
    elif total >= 7 and core:
        tier = "B"
    elif total >= 4:
        tier = "C"
    else:
        tier = "D"
    return {"score": total, "tags": hits, "cocites": co, "tier": tier,
            "has_abstract": bool(work.get("abstract"))}


def authors(work: dict, n: int = 3) -> str:
    names = [a.get("author", {}).get("display_name", "?")
             for a in (work.get("authorships") or [])]
    if not names:
        return "?"
    return ", ".join(names[:n]) + (" et al." if len(names) > n else "")


def venue(work: dict) -> str:
    loc = work.get("primary_location") or {}
    src = (loc.get("source") or {})
    return src.get("display_name") or work.get("type") or ""


def pdf_url(work: dict) -> str:
    for key in ("best_oa_location", "primary_location"):
        loc = work.get(key) or {}
        for f in ("pdf_url", "landing_page_url"):
            if loc.get(f):
                return loc[f]
    return work.get("doi") or ""


# ---------------------------------------------------------------------------
# Reporting
# ---------------------------------------------------------------------------

TSV_COLS = ["tier", "score", "year", "abs", "cocites", "authors", "title",
            "venue", "doi", "tags", "url", "openalex"]


def write_reports(works: list[dict], out: Path, seeds: list[dict],
                  cocite_note: str) -> None:
    works = sorted(works, key=lambda w: (-w["triage"]["score"],
                                         -(w.get("publication_year") or 0)))
    with (out / "triage.tsv").open("w") as fh:
        fh.write("\t".join(TSV_COLS) + "\n")
        for w in works:
            t = w["triage"]
            fh.write("\t".join(str(x).replace("\t", " ") for x in [
                t["tier"], t["score"], w.get("publication_year") or "",
                "y" if t["has_abstract"] else "-",
                len(t["cocites"]), authors(w), (w.get("display_name") or "").strip(),
                venue(w), (w.get("doi") or "").replace("https://doi.org/", ""),
                ",".join(t["tags"]), pdf_url(w), w["id"].rsplit("/", 1)[-1],
            ]) + "\n")

    tiers: dict[str, list[dict]] = {"A": [], "B": [], "C": [], "D": []}
    for w in works:
        tiers[w["triage"]["tier"]].append(w)
    blurb = {
        "A": "Read. Core-lane vocabulary and a high score -- these are the "
             "candidates for a post-2012 solution or a scoop.",
        "B": "Skim the abstract. In the lane, but thin.",
        "C": "Title check only. Diophantine but off-lane.",
        "D": "Noise. Cites the book for background.",
    }
    with (out / "triage.md").open("w") as fh:
        fh.write(f"# OpenAlex forward citations -- triage\n\n")
        fh.write(f"Harvested {utcnow()}. Seeds:\n\n")
        for s in seeds:
            fh.write(f"- `{s['id']}` {s['display_name']} ({s.get('publication_year')}), "
                     f"cited_by_count = {s.get('cited_by_count')}\n")
        fh.write(f"\n{len(works)} distinct citing works. {cocite_note}\n")
        n_abs = sum(1 for w in works if w["triage"]["has_abstract"])
        fh.write(f"\n{n_abs} of {len(works)} records carry an abstract; the rest "
                 "are scored on title, topics and keywords alone, so their scores "
                 "are lower bounds (UPPERCASE tags are title hits, worth double).\n")
        fh.write("\nScoring is keyword-only (see `LEXICON` in the script) plus "
                 "+6 per co-citation; it sorts a reading queue, it does not "
                 "decide anything.\n")
        for tier in "ABCD":
            rows = tiers[tier]
            fh.write(f"\n## Tier {tier} -- {len(rows)} works\n\n{blurb[tier]}\n\n")
            if not rows:
                fh.write("_(none)_\n")
                continue
            for w in rows:
                t = w["triage"]
                co = f" **co-cites {len(t['cocites'])}**" if t["cocites"] else ""
                if not t["has_abstract"]:
                    co += " _(title only -- score is a lower bound)_"
                fh.write(f"- **{t['score']}**{co} &middot; {w.get('publication_year')} "
                         f"&middot; {authors(w)}, *{(w.get('display_name') or '').strip()}*, "
                         f"{venue(w)}. "
                         f"[{(w.get('doi') or pdf_url(w)).replace('https://doi.org/','doi:')}]"
                         f"({pdf_url(w)}) `{','.join(t['tags'])}`\n")


def download_top(works: list[dict], out: Path, n: int, sleep: float) -> None:
    pdfs = out / "pdf"
    pdfs.mkdir(exist_ok=True)
    ranked = sorted(works, key=lambda w: -w["triage"]["score"])[:n]
    for w in ranked:
        loc = w.get("best_oa_location") or {}
        url = loc.get("pdf_url")
        if not url:
            print(f"  no OA pdf: {(w.get('display_name') or '')[:70]}")
            continue
        stem = re.sub(r"[^A-Za-z0-9]+", "-",
                      f"{w.get('publication_year')}-{authors(w, 1)}-"
                      f"{(w.get('display_name') or '')[:40]}").strip("-")
        dest = pdfs / f"{stem}.pdf"
        if dest.exists():
            continue
        try:
            req = urllib.request.Request(url, headers={"User-Agent": UA})
            with urllib.request.urlopen(req, timeout=120) as r:
                data = r.read()
            if not data.startswith(b"%PDF"):
                print(f"  not a pdf: {url}")
                continue
            dest.write_bytes(data)
            print(f"  saved {dest.name} ({len(data)//1024} kB)")
        except Exception as e:  # noqa: BLE001 -- best effort, keep going
            print(f"  failed {url}: {e}")
        time.sleep(sleep)


# ---------------------------------------------------------------------------

def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--seed", action="append", default=None,
                    help="OpenAlex work ID or DOI of the cited work "
                         f"(repeatable; default {DEFAULT_SEEDS[0]} = [Bug12])")
    ap.add_argument("--cocite", action="append", default=[],
                    help="OpenAlex ID or DOI; citers that also cite it get +6 "
                         "and a flag (repeatable)")
    ap.add_argument("--out", default=None, type=Path,
                    help="output directory (default ~/math/scholar/openalex-<slug>)")
    ap.add_argument("--slug", default="bug12", help="name for the default --out")
    ap.add_argument("--mailto", default=os.environ.get("OPENALEX_MAILTO"),
                    help="e-mail for OpenAlex's polite pool. Not set by default: "
                         "passing it publishes the address to OpenAlex.")
    ap.add_argument("--per-page", type=int, default=200)
    ap.add_argument("--sleep", type=float, default=0.2, help="seconds between requests")
    ap.add_argument("--offline", action="store_true",
                    help="re-triage works.jsonl in --out without any network access")
    ap.add_argument("--force", action="store_true", help="refetch even if works.jsonl exists")
    ap.add_argument("--download-top", type=int, default=0, metavar="N",
                    help="also download the OA PDFs of the N best-scoring citers")
    args = ap.parse_args()

    out = args.out or (Path.home() / "math" / "scholar" / f"openalex-{args.slug}")
    out.mkdir(parents=True, exist_ok=True)
    jsonl = out / "works.jsonl"
    log: list = []
    client = Client(args.mailto, args.sleep, log)

    seeds_meta: list[dict] = []
    cocite_ids: set[str] = set()
    cocite_meta: list[dict] = []

    if args.offline:
        if not jsonl.exists():
            raise SystemExit(f"--offline needs an existing {jsonl}")
        works = [json.loads(l) for l in jsonl.open()]
        old = json.loads((out / "meta.json").read_text()) if (out / "meta.json").exists() else {}
        seeds_meta = old.get("seeds", [])
        cocite_meta = old.get("cocites", [])
        cocite_ids = {c["id"] for c in cocite_meta}
        print(f"offline: {len(works)} works from {jsonl}")
    else:
        for ref in (args.seed or DEFAULT_SEEDS):
            wid, w = as_work_id(client, ref)
            seeds_meta.append({"ref": ref, "id": wid,
                               "display_name": w.get("display_name"),
                               "publication_year": w.get("publication_year"),
                               "cited_by_count": w.get("cited_by_count")})
            print(f"seed {wid}: {w.get('display_name')} "
                  f"({w.get('publication_year')}), cited_by_count="
                  f"{w.get('cited_by_count')}")
        for ref in args.cocite:
            wid, w = as_work_id(client, ref)
            cocite_ids.add(wid)
            cocite_meta.append({"ref": ref, "id": wid,
                                "display_name": w.get("display_name")})
            print(f"co-cite marker {wid}: {w.get('display_name')}")

        if jsonl.exists() and not args.force:
            works = [json.loads(l) for l in jsonl.open()]
            print(f"reusing {len(works)} works from {jsonl} (--force to refetch)")
        else:
            works = fetch_citers(client, [s["id"] for s in seeds_meta], args.per_page)
            for w in works:
                w["abstract"] = deinvert(w.pop("abstract_inverted_index", None))
            print(f"fetched {len(works)} distinct citing works")

    for w in works:
        w.setdefault("abstract", "")
        w["triage"] = score(w, cocite_ids)

    with jsonl.open("w") as fh:
        for w in sorted(works, key=lambda w: -w["triage"]["score"]):
            fh.write(json.dumps(w, ensure_ascii=False) + "\n")

    counts: dict[str, int] = {}
    for w in works:
        counts[w["triage"]["tier"]] = counts.get(w["triage"]["tier"], 0) + 1
    (out / "meta.json").write_text(json.dumps({
        "source": "openalex",
        "harvested": utcnow(),
        "seeds": seeds_meta,
        "cocites": cocite_meta,
        "filter": "cites:" + "|".join(s["id"] for s in seeds_meta),
        "select": SELECT,
        "n_works": len(works),
        "tiers": counts,
        "mailto_sent": bool(args.mailto),
        "requests": log,
    }, indent=2, ensure_ascii=False))

    note = (f"Co-citation markers: {', '.join(c['id'] for c in cocite_meta)}."
            if cocite_meta else "No co-citation markers were given.")
    write_reports(works, out, seeds_meta, note)

    print(f"tiers: " + "  ".join(f"{t}={counts.get(t,0)}" for t in "ABCD"))
    print(f"wrote {out}/works.jsonl, triage.tsv, triage.md, meta.json")

    if args.download_top:
        print(f"downloading OA PDFs for the top {args.download_top}...")
        download_top(works, out, args.download_top, args.sleep)
    return 0


if __name__ == "__main__":
    sys.exit(main())
