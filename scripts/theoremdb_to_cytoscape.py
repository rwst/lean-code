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
  scripts/theoremdb_to_cytoscape.py cx2       [theoremdb.json] [-o theorems.cx2]

The cytoscape.js export (convert) is lossless and round-trips; it is for the web
viewer / cytoscape.js, where the style lives in the page.  The CX2 export (cx2) is
a one-file styled network for Cytoscape *Desktop* — lossy (nested fields flattened,
group containers dropped) because CX2 is a visualisation format, not an archive.
"""
from __future__ import annotations

import argparse
import json
import re
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
# theoremdb.json  ->  CX2 (.cx2)   for Cytoscape Desktop, style embedded
# --------------------------------------------------------------------------- #
# Unlike the cytoscape.js export this is NOT lossless: CX2 attribute values must
# be scalars or lists of scalars, so the nested `formalization`/`category` objects
# are flattened into columns, and the compound `group` containers are dropped
# (CX2/Desktop has no compound-parent concept) — `group` survives as a column.
#
# Edit these three maps to restyle the desktop view (they mirror viewer.html):
_NODE_FILL = {  # DISCRETE on the "vis_class" column
    "decl_proved": "#86c08a",
    "decl_cited": "#e2c66b",
    "decl_stated_only": "#d98c8c",
    "informal": "#d4b79b",
    "placeholder": "#eeeeee",
}
_NODE_SHAPE = {"declaration": "round-rectangle", "informal_result": "ellipse"}  # DISCRETE on "node_type"
_EDGE_COLOR = {"states_with": "#7aa7d0", "formal_uses": "#9a7ad0", "informal_uses": "#c08a5a"}  # on "kind"

# Cytoscape Desktop wraps labels only at WHITESPACE, and Lean names have none, so a long
# dotted name (e.g. Bugeaud.problem_10_3_of_waldschmidt) never wraps under NODE_LABEL_MAX_WIDTH
# alone.  We pre-insert "\n" (which Cytoscape renders as a line break) at ./_ boundaries,
# hard-splitting any chunk longer than _WRAP_WIDTH.  Display only — the clean name/key stays
# in its own column.
_WRAP_WIDTH = 18


def _wrap_label(s: str, width: int = _WRAP_WIDTH) -> str:
    lines, cur = [], ""
    for chunk in re.findall(r"[^._]*[._]|[^._]+", s):  # runs ending at '.'/'_', plus a trailing run
        while len(chunk) > width:                       # chunk itself too long: hard-split it
            if cur:
                lines.append(cur)
                cur = ""
            lines.append(chunk[:width])
            chunk = chunk[width:]
        if cur and len(cur) + len(chunk) > width:
            lines.append(cur)
            cur = chunk
        else:
            cur += chunk
    if cur:
        lines.append(cur)
    return "\n".join(lines)

# CX2 attribute columns (declared once in attributeDeclarations).
_CX2_NODE_COLS = {
    "label": "string", "node_type": "string", "vis_class": "string", "name": "string",
    "key": "string", "module": "string", "decl_kind": "string", "status": "string",
    "uses_sorry": "boolean", "category_kind": "string", "category_status": "string",
    "ams": "string", "refs": "list_of_string", "group": "string",
    "statement_tex": "string", "type": "string", "formalized_as": "string",
}
_CX2_EDGE_COLS = {"kind": "string", "interaction": "string", "to_type": "string", "resolved": "boolean"}


def _drop_none(d: dict) -> dict:
    return {k: v for k, v in d.items() if v is not None}


def _cx2_decl_attrs(d: dict) -> dict:
    f = d.get("formalization") or {}
    c = d.get("category") or {}
    status = f.get("status")
    return _drop_none({
        "label": _wrap_label(d["name"]),
        "node_type": "declaration",
        "vis_class": f"decl_{status}" if status else None,
        "name": d["name"],
        "module": d.get("module"),
        "decl_kind": d.get("decl_kind"),
        "status": status,
        "uses_sorry": f.get("uses_sorry"),
        "category_kind": c.get("kind"),
        "category_status": c.get("status"),
        "ams": ",".join(str(a) for a in d.get("ams", [])) or None,
        "refs": d.get("refs") or None,
        "group": d.get("group"),
        "statement_tex": d.get("statement_tex"),
        "type": d.get("type"),
    })


def _cx2_informal_attrs(r: dict) -> dict:
    return _drop_none({
        "label": _wrap_label(r["key"]),
        "node_type": "informal_result",
        "vis_class": "informal",
        "key": r["key"],
        "refs": r.get("refs") or None,
        "statement_tex": r.get("statement_tex"),
        "formalized_as": r.get("formalized_as"),
    })


def _discrete(attr: str, dtype: str, mapping: dict) -> dict:
    return {"type": "DISCRETE",
            "definition": {"attribute": attr, "type": dtype,
                           "map": [{"v": k, "vp": v} for k, v in mapping.items()]}}


def to_cx2(db: dict) -> list:
    import math

    nodes_out: list[dict] = []
    id_of: dict[str, int] = {}

    def add_node(key: str, attrs: dict) -> None:
        id_of[key] = len(nodes_out)
        nodes_out.append({"id": id_of[key], "v": attrs})

    for d in db.get("declarations", []):
        add_node(d["name"], _cx2_decl_attrs(d))
    for r in db.get("informal_results", []):
        add_node(r["key"], _cx2_informal_attrs(r))
    # placeholders for unresolved informal_uses targets (keep the edge valid)
    for e in db.get("edges", []):
        if e["to_type"] == "informal_result" and e["to"] not in id_of:
            add_node(e["to"], {"label": e["to"], "node_type": "informal_result",
                               "vis_class": "placeholder", "key": e["to"]})

    edges_out: list[dict] = []
    dropped = 0
    for e in db.get("edges", []):
        s, t = id_of.get(e["from"]), id_of.get(e["to"])
        if s is None or t is None:  # e.g. an edge into a (dropped) group node
            dropped += 1
            continue
        edges_out.append({"id": len(edges_out), "s": s, "t": t,
                          "v": {"kind": e["kind"], "interaction": e["kind"],
                                "to_type": e["to_type"], "resolved": e["resolved"]}})
    if dropped:
        print(f"note: {dropped} edge(s) dropped (endpoint not a CX2 node)", file=sys.stderr)

    # simple deterministic grid so the import isn't all stacked at the origin
    cols = max(1, math.ceil(math.sqrt(len(nodes_out))))
    for i, n in enumerate(nodes_out):
        n["x"], n["y"] = (i % cols) * 80, (i // cols) * 80

    visual = {
        "default": {
            "network": {"NETWORK_BACKGROUND_COLOR": "#FFFFFF"},
            "node": {
                "NODE_SHAPE": "round-rectangle", "NODE_BACKGROUND_COLOR": "#9bb7d4",
                "NODE_WIDTH": 40.0, "NODE_HEIGHT": 30.0,
                # NODE_LABEL_MAX_WIDTH is the CX2-file name; the importer maps it to Cytoscape's
                # internal NODE_LABEL_WIDTH ("Node Label Width" in the Style GUI). Wrapping itself
                # is forced by the pre-inserted newlines in the "label" column (see _wrap_label).
                "NODE_LABEL_FONT_SIZE": 6, "NODE_LABEL_MAX_WIDTH": 200.0,
                "NODE_LABEL_COLOR": "#202020",
            },
            "edge": {
                "EDGE_WIDTH": 1.5, "EDGE_LINE_COLOR": "#bbbbbb",
                "EDGE_TARGET_ARROW_SHAPE": "triangle", "EDGE_LINE_STYLE": "solid",
            },
        },
        "nodeMapping": {
            "NODE_LABEL": {"type": "PASSTHROUGH", "definition": {"attribute": "label", "type": "string"}},
            "NODE_BACKGROUND_COLOR": _discrete("vis_class", "string", _NODE_FILL),
            "NODE_SHAPE": _discrete("node_type", "string", _NODE_SHAPE),
        },
        "edgeMapping": {
            "EDGE_LINE_COLOR": _discrete("kind", "string", _EDGE_COLOR),
            "EDGE_LINE_STYLE": _discrete("kind", "string", {"informal_uses": "dashed"}),
        },
    }

    return [
        {"CXVersion": "2.0", "hasFragments": False},
        {"metaData": [
            {"name": "attributeDeclarations", "elementCount": 1},
            {"name": "nodes", "elementCount": len(nodes_out)},
            {"name": "edges", "elementCount": len(edges_out)},
            {"name": "visualProperties", "elementCount": 1},
        ]},
        {"attributeDeclarations": [{
            "nodes": {k: {"d": v} for k, v in _CX2_NODE_COLS.items()},
            "edges": {k: {"d": v} for k, v in _CX2_EDGE_COLS.items()},
        }]},
        {"nodes": nodes_out},
        {"edges": edges_out},
        {"visualProperties": [visual]},
        {"status": [{"error": "", "success": True}]},
    ]


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

    x = sub.add_parser("cx2", help="theoremdb.json -> CX2 (.cx2) for Cytoscape Desktop, style embedded")
    x.add_argument("input", nargs="?", default="theoremdb.json")
    x.add_argument("-o", "--output", default="theorems.cx2")

    w = sub.add_parser("webjs", help="theoremdb.json -> theorems-cytoscape.js (window.THEOREMDB; loads over file://)")
    w.add_argument("input", nargs="?", default="theoremdb.json")
    w.add_argument("-o", "--output", default="theorems-cytoscape.js")

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

    if args.cmd == "webjs":
        db = _load(args.input)
        cy = to_cytoscape(db)
        errs = validate_cytoscape_structure(cy)
        if errs:
            for e in errs:
                print(f"  - {e}", file=sys.stderr)
            return 1
        Path(args.output).write_text("window.THEOREMDB = " + json.dumps(cy, ensure_ascii=False) + ";\n")
        print(f"wrote {args.output} (load via <script>; works when app.html is opened over file://)", file=sys.stderr)
        return 0

    if args.cmd == "cx2":
        db = _load(args.input)
        cx = to_cx2(db)
        nodes = next(a["nodes"] for a in cx if "nodes" in a)
        edges = next(a["edges"] for a in cx if "edges" in a)
        Path(args.output).write_text(json.dumps(cx, ensure_ascii=False) + "\n")
        print(f"wrote {args.output}: {len(nodes)} nodes, {len(edges)} edges "
              f"(open in Cytoscape Desktop: File -> Import -> Network from File)", file=sys.stderr)
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
