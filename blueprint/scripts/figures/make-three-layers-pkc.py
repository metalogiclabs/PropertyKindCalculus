#!/usr/bin/env python3
"""The three layers a PropertyKindCalculus capstone is stated over, drawn as one
dataflow seen at three granularities, with the correspondences between them — and,
highlighted, what makes the middle-to-bottom correspondence a *weak bisimulation*.

The layers, top to bottom, and the ladders between them:

  dimension layer      what the laws must satisfy — the image of the hypergraph under
                       the dimension functor `dim` (capstone 3, dimensional homogeneity)
                            ▲ dim: node ↦ dimension, occurrence ↦ family rule
  provenance layer     the metrological provenance hypergraph — what the source
                       declares, and where every kind originates (capstone 1, the seal
                       of a module)
                            ▼ R: the kind-transporting weak bisimulation
  computation layer    the computational tape graph — what the code computes at the
                       recording carrier, no kinds of its own (capstone 2, the seal of
                       the computation)

Both ladders stand on the provenance layer; there is no ladder from the computation
layer to the dimension layer. That is the capstone chapter's "two ladders" point and
the reason the middle band is the kinded one.

Everything on the figure comes from PKC's own source.

  layers      `blueprint/…/Chapters/Capstones.lean`, section "The layers and their
              ladders": the three layers, their objects, and the two ladders.

  hypergraph  `PropertyKindCalculus/Provenance.lean` 568–603: an occurrence relates its
              *ordered* operand nodes to one result node under a witness family; a
              provenance hypergraph is ports, introductions (each with an evidence
              tier), occurrences, and exits. The example is two occurrences: a
              `product` of two ingested quantities and an `additive` combination
              with a minted constant, feeding one exit.

  tape        TorchLean `NN/Runtime/Autograd/Engine/Core/Base.lean` 104–138: a tape is
              a grow-only array of nodes, each one operation with its parent ids in
              operand order; the computational tape graph is the DAG those parents
              determine (`Capstones.lean`, "The seal of the computation — the tape").

  expansion   `PropertyKindCalculus/Complex.lean` 145: at a complex carrier the
              product is `(ac − bd) + (ad + bc)j` — one kinded occurrence becomes four
              multiplications, a subtraction and an addition. The four products are
              the *interior* vertices no hypergraph node names: the silent steps that
              make the bisimulation weak. Addition is componentwise (`Complex.lean`
              142), so the `additive` occurrence expands with no interior at all —
              still several carrier operations for one kinded one, which is one of
              the four reasons R is not a bijection.

  R           `Capstones.lean`, node `cap_def_bisimulation`: total on the observable
              vertices (leaves, roots, the operands and results of every matched
              occurrence), silent on the interior of a carrier-level expansion
              (weak), a simulation in both directions (bi): every occurrence is
              realized by a tape sub-graph whose frontier is the images of its
              operands, and every tape path between observable vertices projects to a
              hypergraph path. Kinds transported along R change only at the image of
              a declared crossing; the example has none.

  dim         `dimension/PropertyKindCalculus/Interaction.lean` 76–84
              (`dim_homomorphism`) and `DimensionalCoverage.lean`: a product adds the
              operand exponents, an additive occurrence keeps the dimension. The top
              band is the hypergraph's image under `dim`, occurrence by occurrence —
              which is what "homomorphism along every occurrence" means.

Drawing decisions that are ours: the three bands share one left-to-right dataflow so
that the eye can follow one value through three granularities; the silent interior
vertices are hollow and gray and carry a τ, the process-algebra mark for a step the
observer does not see; R is the only red on the figure, because it is the
correspondence the slide is about; the band names stand in the left margin so that
nothing crosses them.

The SVG root carries a `viewBox` and no fixed size, so the same file scales to its
container both inlined in the blueprint and as the deck's `<img>`; its marker id is
prefixed per figure because the blueprint's single-page build inlines every figure into
one document.

Usage:  python3 scripts/figures/make-three-layers-pkc.py
        python3 scripts/figures/make-three-layers-pkc.py --out <deck>/three-layers-pkc.svg
"""

from __future__ import annotations

import argparse
import pathlib
from xml.sax.saxutils import escape

HERE = pathlib.Path(__file__).resolve().parent      # blueprint/scripts/figures
FIGURES = HERE.parent.parent / "figures"

RED = "#E4002B"
BLACK = "#000000"
GRAY5 = "#767676"
GRAY2 = "#C8C8C8"
FAINT = "#F3F3F3"

SANS = "Helvetica Neue, Helvetica, Arial, sans-serif"
MONO = "SF Mono, Menlo, Consolas, monospace"

W, H = 960.0, 700.0
BANDS = (  # (top, bottom, margin name, subtitle for the notes column)
    (28.0, 196.0, "DIMENSION", "dimension layer — what the laws must satisfy"),
    (204.0, 388.0, "PROVENANCE", "provenance layer — what the source declares"),
    (396.0, 664.0, "COMPUTATION", "computation layer — what the code computes"),
)
BAND_X0 = 46.0                   # bands start right of the margin names
NOTE_X = 656.0                   # the right-hand column of prose, one block per band
LEAD = 15.0

# The hypergraph's dataflow (middle band); the top band mirrors it 170 px higher.
P = {
    "a": (120.0, 262.0), "b": (170.0, 318.0), "c": (350.0, 288.0),
    "e": (400.0, 348.0), "y": (560.0, 314.0),
}
OCC = {"product": (250.0, 288.0), "additive": (478.0, 314.0)}
OCC_HW = 40.0
DY_DIM = -170.0
DIMS = {"a": "L", "b": "T⁻¹", "c": "L·T⁻¹", "e": "L·T⁻¹", "y": "L·T⁻¹"}
RULES = {"product": "add exponents", "additive": "same dimension"}
KINDS = {"a": "k₁", "b": "k₂", "c": "k₃", "e": "k₃", "y": "k₃"}
TIERS = {"a": "ingest", "b": "ingest", "e": "const"}

# The tape's dataflow (bottom band): named leaves, interior products, and the
# observable results, with the same left-to-right reading as the hypergraph.
T = {
    "a.re": (120.0, 440.0), "a.im": (120.0, 470.0), "b.re": (120.0, 510.0), "b.im": (120.0, 540.0),
    "ac": (215.0, 440.0), "bd": (215.0, 470.0), "ad": (215.0, 510.0), "bc": (215.0, 540.0),
    "c.re": (310.0, 455.0), "c.im": (310.0, 525.0),
    "e.re": (340.0, 590.0), "e.im": (340.0, 620.0),
    "y.re": (430.0, 490.0), "y.im": (430.0, 566.0),
}
LEAVES = ("a.re", "a.im", "b.re", "b.im", "e.re", "e.im")
INTERIOR = ("ac", "bd", "ad", "bc")
ROOTS = ("y.re", "y.im")
OPS = {"ac": "×", "bd": "×", "ad": "×", "bc": "×", "c.re": "−", "c.im": "+", "y.re": "+", "y.im": "+"}
TAPE_EDGES = (
    ("a.re", "ac"), ("b.re", "ac"), ("a.im", "bd"), ("b.im", "bd"),
    ("a.re", "ad"), ("b.im", "ad"), ("a.im", "bc"), ("b.re", "bc"),
    ("ac", "c.re"), ("bd", "c.re"), ("ad", "c.im"), ("bc", "c.im"),
    ("c.re", "y.re"), ("e.re", "y.re"), ("c.im", "y.im"), ("e.im", "y.im"),
)
# R, drawn from each kinded node to each of its observable components.
R_PAIRS = (
    ("a", "a.re"), ("a", "a.im"), ("b", "b.re"), ("b", "b.im"),
    ("c", "c.re"), ("c", "c.im"), ("e", "e.re"), ("e", "e.im"),
    ("y", "y.re"), ("y", "y.im"),
)
# The realization of each occurrence: a dotted box around its tape sub-graph.
REALIZATIONS = {
    "product": (188.0, 422.0, 344.0, 556.0),
    "additive": (404.0, 470.0, 458.0, 588.0),
}


def txt(x: float, y: float, s: str, *, size: float = 12.0, fill: str = BLACK,
        anchor: str = "start", family: str | None = None, weight: str | None = None,
        style: str | None = None, rotate: float | None = None, raw: bool = False) -> str:
    a = [f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size:.1f}" fill="{fill}"']
    if anchor != "start":
        a.append(f' text-anchor="{anchor}"')
    if family:
        a.append(f' font-family="{family}"')
    if weight:
        a.append(f' font-weight="{weight}"')
    if style:
        a.append(f' font-style="{style}"')
    if rotate is not None:
        a.append(f' transform="rotate({rotate:.0f} {x:.1f} {y:.1f})"')
    a.append(">")
    a.append(s if raw else escape(s))
    a.append("</text>")
    return "".join(a)


def line(x1: float, y1: float, x2: float, y2: float, *, stroke: str = BLACK,
         w: float = 1.4, dash: str | None = None, marker: str | None = None) -> str:
    d = f' stroke-dasharray="{dash}"' if dash else ""
    m = f' marker-end="url(#layers-{marker})"' if marker else ""
    return (f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
            f'stroke="{stroke}" stroke-width="{w:.1f}"{d}{m}/>')


def circle(x: float, y: float, r: float, *, fill: str = BLACK, stroke: str = BLACK,
           w: float = 1.4) -> str:
    return (f'<circle cx="{x:.1f}" cy="{y:.1f}" r="{r:.1f}" fill="{fill}" '
            f'stroke="{stroke}" stroke-width="{w:.1f}"/>')


def rrect(x0: float, y0: float, x1: float, y1: float, *, fill: str = "none",
          stroke: str = BLACK, w: float = 1.4, dash: str | None = None,
          r: float = 6.0) -> str:
    d = f' stroke-dasharray="{dash}"' if dash else ""
    return (f'<rect x="{x0:.1f}" y="{y0:.1f}" width="{x1 - x0:.1f}" height="{y1 - y0:.1f}" '
            f'rx="{r:.1f}" fill="{fill}" stroke="{stroke}" stroke-width="{w:.1f}"{d}/>')


def wrap(x: float, y: float, lines: list[str], *, size: float = 11.5, lead: float = LEAD,
         fill: str = BLACK) -> str:
    """A block of prose, one <text> per line; a line starting with '!' is bold, and
    one starting with '#' is the band's subtitle: bold and black."""
    out = []
    for i, s in enumerate(lines):
        if s.startswith("#"):
            out.append(txt(x, y + i * lead, s[1:], size=size, fill=BLACK, weight="700"))
        elif s.startswith("!"):
            out.append(txt(x, y + i * lead, s[1:], size=size, fill=fill, weight="700"))
        else:
            out.append(txt(x, y + i * lead, s, size=size, fill=fill))
    return "".join(out)


def defs() -> str:
    return (
        '<defs>'
        f'<marker id="layers-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" '
        f'markerHeight="7" orient="auto-start-reverse">'
        f'<path d="M 0 0 L 10 5 L 0 10 z" fill="{GRAY5}"/></marker>'
        '</defs>'
    )


def bands() -> str:
    o = []
    for i, (t, b, name, _sub) in enumerate(BANDS):
        o.append(rrect(BAND_X0, t, W - 14, b, fill=FAINT if i == 1 else "none",
                       stroke=GRAY2, w=1.0, r=8))
        o.append(txt(30, (t + b) / 2, name, size=11.0, fill=GRAY5, weight="700",
                     anchor="middle", rotate=-90))
    return "".join(o)


def pill_hw(s: str) -> float:
    return 8.0 + 4.4 * len(s)


def hyperedge(name: str, cx: float, cy: float, operands: list[str], result: str,
              *, dy: float = 0.0, label: str | None = None, mono: bool = True,
              port_hw=lambda n: 13.0) -> str:
    """A hyperedge as a small box; operand lines enter from the left, the result leaves
    to the right — order on the box is the operand order."""
    o = []
    hw, hh = OCC_HW, 12.0
    o.append(rrect(cx - hw, cy - hh + dy, cx + hw, cy + hh + dy, stroke=BLACK, w=1.2, r=4))
    o.append(txt(cx, cy + 4 + dy, label or name, size=10.5, anchor="middle",
                 family=MONO if mono else None))
    for op in operands:
        x, y = P[op]
        o.append(line(x + port_hw(op), y + dy, cx - hw, cy + dy, w=1.2))
    x, y = P[result]
    o.append(line(cx + hw, cy + dy, x - port_hw(result), y + dy, w=1.2))
    return "".join(o)


def kinded_node(name: str) -> str:
    x, y = P[name]
    o = [circle(x, y, 12.0), txt(x, y + 4.5, name, size=12.0, fill="#FFFFFF", anchor="middle",
                                  family=MONO, weight="700")]
    o.append(txt(x, y - 17, KINDS[name], size=10.5, anchor="middle", family=MONO, fill=GRAY5))
    if name in TIERS:
        o.append(txt(x, y + 26, TIERS[name], size=9.5, anchor="middle", fill=GRAY5, style="italic"))
    return "".join(o)


def dim_node(name: str) -> str:
    x, y = P[name]
    y += DY_DIM
    s = DIMS[name]
    hw = pill_hw(s)
    return (rrect(x - hw, y - 11, x + hw, y + 11, stroke=GRAY5, w=1.1, r=11) +
            txt(x, y + 4, s, size=11.5, anchor="middle", family=MONO))


def tape_vertex(name: str) -> str:
    x, y = T[name]
    o = []
    if name in LEAVES:
        o.append(circle(x, y, 8.5))
        o.append(txt(x - 13, y + 4, name, size=10.5, anchor="end", family=MONO))
        if name.startswith("e."):
            o.append(txt(x - 13, y + 15, "const", size=9.0, anchor="end", fill=GRAY5, style="italic"))
    elif name in INTERIOR:
        o.append(circle(x, y, 8.5, fill="#FFFFFF", stroke=GRAY5, w=1.4))
        o.append(txt(x, y + 4, OPS[name], size=11.0, anchor="middle", fill=GRAY5, weight="700"))
        o.append(txt(x + 8, y + 13, "τ", size=10.0, fill=GRAY5, style="italic"))
    else:
        if name in ROOTS:
            o.append(circle(x, y, 12.0, fill="none", stroke=BLACK, w=1.2))
        o.append(circle(x, y, 8.5, fill="#FFFFFF"))
        o.append(txt(x, y + 4, OPS[name], size=11.0, anchor="middle", weight="700"))
        o.append(txt(x + (18 if name in ROOTS else 13), y + 4, name, size=10.5, family=MONO))
    return "".join(o)


def build() -> str:
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W:.0f} {H:.0f}" '
         f'font-family="{SANS}">',
         f'<rect width="{W:.0f}" height="{H:.0f}" fill="#FFFFFF"/>', defs(), bands()]

    # --- the dimension layer: the hypergraph's image under dim -----------------
    for name in ("a", "b", "c", "e", "y"):
        o.append(dim_node(name))
    for occ, (cx, cy) in OCC.items():
        ops = ["a", "b"] if occ == "product" else ["c", "e"]
        res = "c" if occ == "product" else "y"
        o.append(hyperedge(occ, cx, cy, ops, res, dy=DY_DIM, label=RULES[occ], mono=False,
                           port_hw=lambda n: pill_hw(DIMS[n])))
    # dim, node by node and occurrence by occurrence: the functor is the arrows.
    for name in ("a", "b", "c", "e", "y"):
        x, y = P[name]
        o.append(line(x, y - 14, x, y + DY_DIM + 14, stroke=GRAY5, w=1.0, marker="arrow"))
    for occ, (cx, cy) in OCC.items():
        o.append(line(cx, cy - 13, cx, cy + DY_DIM + 13, stroke=GRAY5, w=1.0, marker="arrow"))
    o.append(txt(568, 178, "dim", size=10.5, fill=GRAY5, family=MONO))

    # --- the provenance layer: the hypergraph itself --------------------------
    o.append(hyperedge("product", *OCC["product"], ["a", "b"], "c"))
    o.append(hyperedge("additive", *OCC["additive"], ["c", "e"], "y"))
    for name in ("a", "b", "c", "e", "y"):
        o.append(kinded_node(name))
    yx, yy = P["y"]
    o.append(line(yx + 13, yy, yx + 48, yy, w=1.2, marker="arrow"))
    o.append(txt(yx + 52, yy + 4, "exit", size=10.0, fill=GRAY5, style="italic"))

    # --- the computation layer: the tape graph --------------------------------
    for occ, (x0, y0, x1, y1) in REALIZATIONS.items():
        o.append(rrect(x0, y0, x1, y1, stroke=GRAY5, w=1.1, dash="2 3", r=8))
    o.append(txt(188, 570, "product ↦", size=9.5, fill=GRAY5, family=MONO))
    o.append(txt(188, 582, "(ac−bd) + (ad+bc)j", size=9.5, fill=GRAY5, family=MONO))
    o.append(txt(404, 602, "additive ↦ componentwise", size=9.5, fill=GRAY5, family=MONO))
    for u, v in TAPE_EDGES:
        (x1, y1), (x2, y2) = T[u], T[v]
        o.append(line(x1 + 9, y1, x2 - 9, y2, w=1.0,
                      stroke=GRAY5 if (u in INTERIOR or v in INTERIOR) else BLACK))
    for name in T:
        o.append(tape_vertex(name))

    # --- R, the one red thing on the figure -----------------------------------
    for hn, tv in R_PAIRS:
        (x1, y1), (x2, y2) = P[hn], T[tv]
        o.append(line(x1, y1 + 13, x2, y2 - 10, stroke=RED, w=1.1, dash="4 3"))
    o.append(txt(392, 406, "R", size=14.0, fill=RED, weight="700", style="italic"))

    # --- the right-hand column ------------------------------------------------
    o.append(wrap(NOTE_X, 50, [
        "#" + BANDS[0][3],
        "!capstone 3 — dimensional homogeneity",
        "dim is a functor: each node to its dimension,",
        "each occurrence to its family's rule. The band",
        "is the hypergraph's image under dim; the",
        "capstone says the image is exact along every",
        "occurrence, so an output's dimension is",
        "computed from the sources' alone. A wrong",
        "edge, ω·τ → ω, has no image here: refuted.",
    ], fill=GRAY5))
    o.append(wrap(NOTE_X, 228, [
        "#" + BANDS[1][3],
        "!capstone 1 — the seal of a module",
        "The metrological provenance hypergraph; kinds",
        "originate here. Every leaf of an output's",
        "pedigree is a declared source — a checked",
        "ingest, a constant mint, an attestation — so",
        "no undeclared raw datum reaches y. Decided",
        "per boundary by the kernel; stated over this",
        "graph, not over the code.",
    ]))
    o.append(wrap(NOTE_X, 420, [
        "#" + BANDS[2][3],
        "The computational tape graph, with no kinds of its own.",
        "!R — the kind-transporting weak bisimulation",
        "total: every observable vertex (a leaf, a root,",
        "an operand or result of a matched occurrence)",
        "has exactly one kinded partner;",
        "weak: the interior vertices τ of a carrier",
        "expansion are silent — no kinded node names ac;",
        "bi: every occurrence is realized by a sub-graph",
        "(down), every tape path between observable",
        "vertices projects to a hypergraph path (up).",
        "Not a bijection: one kinded operation is several",
        "carrier operations, and compaction merges.",
        "!capstone 2 — the seal of the computation",
        "The seal carried onto the tape at every carrier:",
        "y depends only on the images of its influencers.",
    ], fill=GRAY5))

    # --- the key, on the bottom rule ------------------------------------------
    ky = 686.0
    o.append(circle(60, ky - 4, 6.0))
    o.append(txt(72, ky, "declared node / observable vertex", size=10.5, fill=GRAY5))
    o.append(circle(280, ky - 4, 6.0, fill="#FFFFFF", stroke=GRAY5))
    o.append(txt(292, ky, "silent interior vertex τ", size=10.5, fill=GRAY5))
    o.append(rrect(440, ky - 11, 464, ky + 1, stroke=GRAY5, w=1.1, dash="2 3", r=3))
    o.append(txt(472, ky, "realization of one occurrence", size=10.5, fill=GRAY5))
    o.append(line(650, ky - 4, 680, ky - 4, stroke=RED, w=1.1, dash="4 3"))
    o.append(txt(688, ky, "R", size=10.5, fill=RED, weight="700", style="italic"))
    o.append(line(720, ky - 4, 750, ky - 4, stroke=GRAY5, w=1.0, marker="arrow"))
    o.append(txt(758, ky, "dim, a functor along every occurrence", size=10.5, fill=GRAY5))

    o.append("</svg>")
    return "".join(o)


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    out = pathlib.Path(args.out) if args.out else FIGURES / "three-layers-pkc.svg"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(build(), encoding="utf-8")
    print(f"{out}  {out.stat().st_size:,} bytes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
