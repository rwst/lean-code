#!/usr/bin/env python3
# (C) 2026 Ralf Stephan, in collaboration with Claude Code.
# Released under CC0 1.0 Universal (public-domain dedication).
# See https://creativecommons.org/publicdomain/zero/1.0/
"""
theoremdb.json  <->  cytoscape.js elements JSON

Embeds the canonical theorem-database extract into the cytoscape.js graph format
(https://js.cytoscape.org/#notation/elements-json) and back again, losslessly.

Mapping
-------
  declarations[]      -> nodes  (class "declaration"),     id = "decl:"     + name
  informal_results[]  -> nodes  (class "informal_result"), id = "informal:" + key
  groups[]            -> compound parent nodes ("group"),  id = "group:"    + key
  edges[]             -> edges   (class = kind),            id = kind ":" from "->" to
  schema_version / generated / stats -> graph-level `data` (top level of cy.json())

Faithfulness rules (the four that make it lossless; see the design notes):
  1. Global id namespace is unified by prefixing every node id with its class
     ("decl:", "informal:", "group:"), so the three theoremdb key-spaces can never
     collide.  The class is also recorded in `data.node_type` and `classes`.
  2. Edge ids embed `kind`, so two endpoints joined by more than one edge kind
     stay distinct.
  3. An `informal_uses` edge with resolved=false points at a registry key that has
     no informal_result record.  cytoscape silently drops edges whose endpoints do
     not exist, so a tagged placeholder node (`data._placeholder = true`) is
     materialised for that target.  On the way back, placeholder nodes are dropped,
     so they never leak into informal_results[].
  4. Top-level provenance (schema_version / generated / stats) has no home in the
     bare elements array, so it lives in the graph-level `data` object that cy.json()
     supports.  `elements` alone is still valid cytoscape input.

Every original record is copied verbatim into `data` (minus the synthetic
id/parent/source/target/node_type keys), so presence/absence of optional fields is
preserved exactly and the inverse is a pure projection.

Usage
-----
  scripts/theoremdb_to_cytoscape.py convert   [theoremdb.json] [-o cytoscape.json]
  scripts/theoremdb_to_cytoscape.py invert    [cytoscape.json] [-o theoremdb.json]
  scripts/theoremdb_to_cytoscape.py roundtrip  [theoremdb.json]   # convert+invert+verify
"""
from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

# Synthetic keys this converter injects; stripped on the way back so the inverse is exact.
_NODE_SYNTHETIC = {"id", "parent", "node_type"}
_EDGE_SYNTHETIC = {"id", "source", "target", "node_type"}

_ID_PREFIX = {"declaration": "decl:", "informal_result": "informal:", "group": "group:"}


# --------------------------------------------------------------------------- #
# theoremdb.json  ->  cytoscape.js
# --------------------------------------------------------------------------- #
def to_cytoscape(db: dict) -> dict:
    nodes: list[dict] = []
    edges: list[dict] = []

    decl_ids = {f"decl:{d['name']}" for d in db.get("declarations", [])}
    informal_ids = {f"informal:{r['key']}" for r in db.get("informal_results", [])}
    group_keys = {g["key"] for g in db.get("groups", [])}

    # declarations -> nodes; group membership -> compound `parent`
    for d in db.get("declarations", []):
        data = {"id": f"decl:{d['name']}", "node_type": "declaration", **d}
        grp = d.get("group")
        if grp is not None and grp in group_keys:
            data["parent"] = f"group:{grp}"
        nodes.append({"group": "nodes", "classes": "declaration", "data": data})

    # informal_results -> nodes
    for r in db.get("informal_results", []):
        data = {"id": f"informal:{r['key']}", "node_type": "informal_result", **r}
        nodes.append({"group": "nodes", "classes": "informal_result", "data": data})

    # groups -> compound parent nodes (members already carry `parent`, set above)
    for g in db.get("groups", []):
        data = {"id": f"group:{g['key']}", "node_type": "group", **g}
        nodes.append({"group": "nodes", "classes": "group", "data": data})

    # edges -> edges; materialise placeholders for unresolved informal targets
    for e in db.get("edges", []):
        src = f"decl:{e['from']}"
        if e["to_type"] == "declaration":
            tgt = f"decl:{e['to']}"
        else:  # informal_result
            tgt = f"informal:{e['to']}"
            if tgt not in informal_ids:
                # rule 3: keep the edge alive with a tagged placeholder node
                informal_ids.add(tgt)
                nodes.append(
                    {
                        "group": "nodes",
                        "classes": "informal_result placeholder",
                        "data": {
                            "id": tgt,
                            "node_type": "informal_result",
                            "key": e["to"],
                            "_placeholder": True,
                        },
                    }
                )
        eid = f"{e['kind']}:{e['from']}->{e['to']}"
        edges.append(
            {"group": "edges", "classes": e["kind"], "data": {"id": eid, "source": src, "target": tgt, **e}}
        )

    cy: dict = {"elements": {"nodes": nodes, "edges": edges}, "data": {}}
    for k in ("schema_version", "generated", "stats"):
        if k in db:
            cy["data"][k] = db[k]
    return cy


# --------------------------------------------------------------------------- #
# cytoscape.js  ->  theoremdb.json   (pure projection: drop synthetic keys)
# --------------------------------------------------------------------------- #
def from_cytoscape(cy: dict) -> dict:
    elements = cy.get("elements", cy)
    if isinstance(elements, list):  # flat-array form
        nodes = [el for el in elements if el.get("group") != "edges" and "source" not in el.get("data", {})]
        edges = [el for el in elements if el.get("group") == "edges" or "source" in el.get("data", {})]
    else:
        nodes = elements.get("nodes", [])
        edges = elements.get("edges", [])

    declarations, informal_results, groups = [], [], []
    for n in nodes:
        data = n["data"]
        if data.get("_placeholder"):
            continue  # rule 3: placeholders never re-enter informal_results
        rec = {k: v for k, v in data.items() if k not in _NODE_SYNTHETIC}
        nt = data["node_type"]
        if nt == "declaration":
            declarations.append(rec)
        elif nt == "informal_result":
            informal_results.append(rec)
        elif nt == "group":
            groups.append(rec)
        else:
            raise ValueError(f"unknown node_type {nt!r} on {data.get('id')!r}")

    edge_recs = [{k: v for k, v in e["data"].items() if k not in _EDGE_SYNTHETIC} for e in edges]

    db: dict = {}
    meta = cy.get("data", {})
    for k in ("schema_version", "generated"):
        if k in meta:
            db[k] = meta[k]
    db["declarations"] = declarations
    db["informal_results"] = informal_results
    db["groups"] = groups
    db["edges"] = edge_recs
    if "stats" in meta:
        db["stats"] = meta["stats"]
    return db


# --------------------------------------------------------------------------- #
# Validators
# --------------------------------------------------------------------------- #
def validate_cytoscape_structure(cy: dict) -> list[str]:
    """cytoscape's own invariants: unique ids, edge endpoints resolve, parents resolve."""
    errs: list[str] = []
    elements = cy.get("elements", {})
    nodes = elements.get("nodes", [])
    edges = elements.get("edges", [])

    node_ids: set[str] = set()
    for n in nodes:
        nid = n["data"]["id"]
        if nid in node_ids:
            errs.append(f"duplicate node id: {nid}")
        node_ids.add(nid)

    all_ids = set(node_ids)
    for e in edges:
        eid = e["data"]["id"]
        if eid in all_ids:
            errs.append(f"edge id collides with existing id: {eid}")
        all_ids.add(eid)

    for e in edges:
        for end in ("source", "target"):
            ref = e["data"][end]
            if ref not in node_ids:
                errs.append(f"edge {e['data']['id']}: {end} {ref!r} has no node")

    for n in nodes:
        parent = n["data"].get("parent")
        if parent is not None and parent not in node_ids:
            errs.append(f"node {n['data']['id']}: parent {parent!r} has no node")
    return errs


def _diff(a, b, path: str = "") -> list[str]:
    """Semantic diff: dict order ignored, list order significant. Reports first mismatches."""
    out: list[str] = []
    if type(a) is not type(b) and not (isinstance(a, (int, float)) and isinstance(b, (int, float))):
        return [f"{path or '<root>'}: type {type(a).__name__} != {type(b).__name__}"]
    if isinstance(a, dict):
        for k in a.keys() | b.keys():
            if k not in a:
                out.append(f"{path}.{k}: missing on left")
            elif k not in b:
                out.append(f"{path}.{k}: missing on right")
            else:
                out += _diff(a[k], b[k], f"{path}.{k}")
    elif isinstance(a, list):
        if len(a) != len(b):
            out.append(f"{path}: list length {len(a)} != {len(b)}")
        for i, (x, y) in enumerate(zip(a, b)):
            out += _diff(x, y, f"{path}[{i}]")
    elif a != b:
        out.append(f"{path}: {a!r} != {b!r}")
    return out


def roundtrip(db: dict) -> tuple[list[str], list[str]]:
    """Return (structural_errors, roundtrip_diffs). Empty/empty means lossless."""
    cy = to_cytoscape(db)
    structural = validate_cytoscape_structure(cy)
    db2 = from_cytoscape(cy)
    diffs = _diff(db, db2)
    return structural, diffs


# --------------------------------------------------------------------------- #
# CLI
# --------------------------------------------------------------------------- #
def _load(path: str) -> dict:
    return json.loads(Path(path).read_text())


def _dump(obj: dict, out: str | None) -> None:
    text = json.dumps(obj, indent=2, ensure_ascii=False)
    if out:
        Path(out).write_text(text + "\n")
        print(f"wrote {out}", file=sys.stderr)
    else:
        print(text)


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    c = sub.add_parser("convert", help="theoremdb.json -> cytoscape.js")
    c.add_argument("input", nargs="?", default="theoremdb.json")
    c.add_argument("-o", "--output")

    i = sub.add_parser("invert", help="cytoscape.js -> theoremdb.json")
    i.add_argument("input", nargs="?", default="cytoscape.json")
    i.add_argument("-o", "--output")

    r = sub.add_parser("roundtrip", help="convert+invert+verify lossless")
    r.add_argument("input", nargs="?", default="theoremdb.json")

    args = p.parse_args(argv)

    if args.cmd == "convert":
        db = _load(args.input)
        cy = to_cytoscape(db)
        errs = validate_cytoscape_structure(cy)
        if errs:
            print("cytoscape structural errors:", file=sys.stderr)
            for e in errs:
                print(f"  - {e}", file=sys.stderr)
            return 1
        n = len(cy["elements"]["nodes"])
        m = len(cy["elements"]["edges"])
        print(f"{n} nodes, {m} edges", file=sys.stderr)
        _dump(cy, args.output)
        return 0

    if args.cmd == "invert":
        cy = _load(args.input)
        _dump(from_cytoscape(cy), args.output)
        return 0

    if args.cmd == "roundtrip":
        db = _load(args.input)
        structural, diffs = roundtrip(db)
        ok = True
        if structural:
            ok = False
            print("FAIL: cytoscape structural errors:", file=sys.stderr)
            for e in structural:
                print(f"  - {e}", file=sys.stderr)
        if diffs:
            ok = False
            print(f"FAIL: round-trip lost information ({len(diffs)} diffs):", file=sys.stderr)
            for d in diffs[:40]:
                print(f"  - {d}", file=sys.stderr)
            if len(diffs) > 40:
                print(f"  ... and {len(diffs) - 40} more", file=sys.stderr)
        if ok:
            cy = to_cytoscape(db)
            counts = (
                len(db.get("declarations", [])),
                len(db.get("informal_results", [])),
                len(db.get("groups", [])),
                len(db.get("edges", [])),
            )
            print(
                f"OK: lossless round-trip "
                f"({counts[0]} declarations, {counts[1]} informal_results, "
                f"{counts[2]} groups, {counts[3]} edges -> "
                f"{len(cy['elements']['nodes'])} nodes + {len(cy['elements']['edges'])} edges)"
            )
        return 0 if ok else 1

    return 2


if __name__ == "__main__":
    raise SystemExit(main())
