#!/usr/bin/env python3
"""Lowe's ontological square, labeled with the PropertyKindCalculus vocabulary it
is implemented as, and showing where the calculus's parameters live.

This is the *explanatory* figure, as against the wordless mark (`pkc_icon.py`,
which the architecture cake uses for its PKC band): full words at the corners
and on the edges, because the point of the slide is that the audience can read
the square and decode `k` and `R` from it. It is deliberately free of any particular model's vocabulary — each
corner's instance slot is an empty `<...>`, so the figure states the shape and
nothing else.

Everything on the figure comes from PKC's own source.

  corners   `blueprint/…/Chapters/Foundations.lean` 141–144 assigns them, and it
            is worth quoting exactly, because the assignment is not the obvious
            one: "`SortOfSystem` is his *Kinds* (the substantial universal), the
            object index his *Substances* (the substantial particular),
            `KindOfProperty` his *Attributes* (the non-substantial universal),
            `IndividualQuantity` his *Modes*." `Foundations.lean` 97–104 states
            the same correspondence in the library's own words.

  edges     same file, 144–151. `Sorted.sortOf` is the left *instantiated by*
            edge; the kind index is the right one; the object index is the
            bottom *characterized by* edge; `DedicatedKind` is the top one. Of
            these the middle two are singled out — "both edges into the mode are
            carried in the *type* of an individual quantity, which is what puts
            the arithmetic under the type checker" — so the figure draws those
            two at three times the weight of the others, and keys the weight
            once. That chapter also notes, and the figure follows it, that these
            are structure *parameters* in Lean's own vocabulary; it says *index*
            to name the role, which is that each is fixed in the type of a given
            quantity.

  diagonal  same file, 153–162. Exemplification "is derivative for him,
            factoring through either path around the square, and the calculus
            likewise has no primitive object-to-kind-of-property construct."
            Hence dashed, and labeled as derived by either PATH AROUND the
            square — up the left edge then across the top, or across the bottom
            then up the right. It is not a relation that runs in two directions
            along itself, and a label saying "either way round" was read that
            way, so it does not say that.

  signature `IndividualQuantity.lean` 73 — `structure IndividualQuantity
            {O : Type u} (o : O) (k : KindOfProperty) (R : Type)`. The parameter
            names on the figure are the real ones: `o` and `k` lowercase, `R`
            upper.

  carriers  `Quantity.lean` 361–400: `Nat` and `Int` are `LawfulCarrier`s,
            `Float` is a `Carrier` and deliberately not lawful ("floating-point
            addition is not associative, so the additivity laws are
            intentionally unavailable here"); `dimension/…/QuantityReal.lean`
            29–35 gives `ℝ`. `Float32` carries a mode in a committed exhibit —
            `ForPhysLib/Exhibits/TwoRovers/Findings.lean` 258 evaluates
            `IndividualQuantity (partOf rover1 p) massK Float32` to `10.0` — so
            the plate stack is an observed fact about the same M corner at four
            carriers, not an illustration.

Three drawing decisions are ours rather than quotations.

The columns and rows are braced, because the square's whole content is a 2×2:
universals over particulars, substantial beside non-substantial. A brace was
chosen over a ruled span or a tinted band because both of those proved too
quiet to register against a figure that is already made of rules. Each brace
encloses everything in its row or column — so the particulars brace is tall,
since the carrier plates belong to the M corner.

Naming the columns also defuses a collision the vocabulary cannot avoid: Lowe's
*Kinds* corner is a kind of SYSTEM, while `KindOfProperty` is a kind of PROPERTY
and is the *Attributes* corner. With the columns braced and named, the two
senses of the word are visibly in different columns, so the `k` of
`Quantity k R` reads as A and not K without a caption having to say so.

And the carrier is drawn OUT of the plane. Kind parametricity moves within the
square: a different `k` is a different point of the A corner, which the red
right edge already carries. `R` is not an ontological category, has no corner
and no edge, and only M is indexed by it — so it shows as plates behind M while
the other three corners stay put. Stacking the whole square per carrier would
pictorially claim the ontology changes with the number type, which is false.

The SVG root carries a `viewBox` and no fixed size, so the same file scales to its
container both inlined in the blueprint and as the deck's `<img>`.

Usage:  python3 scripts/figures/make-lowe-square-pkc.py
        python3 scripts/figures/make-lowe-square-pkc.py --out <deck>/lowe-square-pkc.svg
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

SANS = "Helvetica Neue, Helvetica, Arial, sans-serif"
MONO = "SF Mono, Menlo, Consolas, monospace"

W, H = 960.0, 440.0
CXL, CXR = 270.0, 760.0          # corner columns: substantial | non-substantial
CYT, CYB = 96.0, 266.0           # corner rows:    universal   | particular
THIN, THICK = 1.6, 4.8           # an ordinary edge, and a type index
CARD_HW = 106.0                  # the M corner is a card, because M has depth
CARD_T, CARD_B = CYB - 28.0, CYB + 62.0
# The carrier axis recedes almost straight DOWN. The vertical step has to
# exceed a plate label's cap height or the next plate's bottom rule strikes
# through the name; with that much vertical separation the sideways step only
# has to be wide enough to show an edge, so it is one character wide.
PLATE_DX, PLATE_DY = 9.0, 26.0
PLATES = (("R=Float32", 3), ("R=Float", 2), ("R=ℝ", 1))
SLOT = "<...>"                   # the instance slot, left for a model to fill

BRACE_W = 18.0                   # how far a brace's cusp stands off its arms
COL_ARMS_Y = 66.0                # column braces sit just above the top row
ROW_ARMS_X = 190.0               # row braces sit just left of the left column
# A column's brace spans everything in the column, so the right-hand one reaches
# past the M card to take in the carrier plates.
COLUMNS = (((205.0, 335.0), "substantial — systems"),
           ((645.0, 895.0), "non-substantial — properties"))
ROWS = (((82.0, 135.0), "universals"),
        ((CARD_T, CARD_B + 3 * PLATE_DY), "particulars"))


def txt(x: float, y: float, s: str, *, size: float = 12.0, fill: str = BLACK,
        anchor: str = "start", family: str | None = None,
        weight: str | None = None, style: str | None = None,
        raw: bool = False) -> str:
    a = [f'<text x="{x:.1f}" y="{y:.1f}" font-size="{size:.1f}" fill="{fill}"']
    if anchor != "start":
        a.append(f' text-anchor="{anchor}"')
    if family:
        a.append(f' font-family="{family}"')
    if weight:
        a.append(f' font-weight="{weight}"')
    if style:
        a.append(f' font-style="{style}"')
    a.append(">")
    a.append(s if raw else escape(s))
    a.append("</text>")
    return "".join(a)


def line(x1: float, y1: float, x2: float, y2: float, *, stroke: str = BLACK,
         w: float = THIN, dash: str | None = None) -> str:
    d = f' stroke-dasharray="{dash}"' if dash else ""
    return (f'<line x1="{x1:.1f}" y1="{y1:.1f}" x2="{x2:.1f}" y2="{y2:.1f}" '
            f'stroke="{stroke}" stroke-width="{w:.2f}"{d}/>')


def path(d: str, *, stroke: str = GRAY5, w: float = 1.8) -> str:
    return (f'<path d="{d}" fill="none" stroke="{stroke}" stroke-width="{w:.2f}" '
            f'stroke-linecap="round" stroke-linejoin="round"/>')


def brace_v(xa: float, y0: float, y1: float, w: float = BRACE_W) -> str:
    """A curly brace spanning y0..y1: arms at `xa`, cusp pointing left."""
    xs, xt, ym = xa - w * 0.55, xa - w, (y0 + y1) / 2
    q = min(w * 0.9, (ym - y0) * 0.45)
    return path(
        f'M {xa:.1f} {y0:.1f} Q {xs:.1f} {y0:.1f} {xs:.1f} {y0 + q:.1f} '
        f'L {xs:.1f} {ym - q:.1f} Q {xs:.1f} {ym:.1f} {xt:.1f} {ym:.1f} '
        f'Q {xs:.1f} {ym:.1f} {xs:.1f} {ym + q:.1f} L {xs:.1f} {y1 - q:.1f} '
        f'Q {xs:.1f} {y1:.1f} {xa:.1f} {y1:.1f}')


def brace_h(ya: float, x0: float, x1: float, w: float = BRACE_W) -> str:
    """A curly brace spanning x0..x1: arms at `ya`, cusp pointing up."""
    ys, yt, xm = ya - w * 0.55, ya - w, (x0 + x1) / 2
    q = min(w * 0.9, (xm - x0) * 0.45)
    return path(
        f'M {x0:.1f} {ya:.1f} Q {x0:.1f} {ys:.1f} {x0 + q:.1f} {ys:.1f} '
        f'L {xm - q:.1f} {ys:.1f} Q {xm:.1f} {ys:.1f} {xm:.1f} {yt:.1f} '
        f'Q {xm:.1f} {ys:.1f} {xm + q:.1f} {ys:.1f} L {x1 - q:.1f} {ys:.1f} '
        f'Q {x1:.1f} {ys:.1f} {x1:.1f} {ya:.1f}')


def scope() -> str:
    """Brace each column and each row, and name it outside its cusp."""
    o: list[str] = []
    for (x0, x1), head in COLUMNS:
        o.append(brace_h(COL_ARMS_Y, x0, x1))
        o.append(txt((x0 + x1) / 2, COL_ARMS_Y - BRACE_W - 8, head, size=12.5,
                     fill=GRAY5, anchor="middle"))
    for (y0, y1), lab in ROWS:
        o.append(brace_v(ROW_ARMS_X, y0, y1))
        o.append(txt(ROW_ARMS_X - BRACE_W - 10, (y0 + y1) / 2 + 4, lab,
                     size=12.5, fill=GRAY5, anchor="end"))
    return "".join(o)


def corner(cx: float, cy: float, name: str, ident: str, *,
           color: str = BLACK, ident_raw: bool = False) -> str:
    """A corner: Lowe's name, the PKC identifier under it, an empty slot under
    that. Three registers, so the audience can tell whose word is whose — bold
    sans is Lowe's, mono is the library's, gray mono is what a model supplies.
    """
    return "".join((
        txt(cx, cy - 1, name, size=18, weight="700", fill=color, anchor="middle"),
        txt(cx, cy + 17, ident, size=13, family=MONO, fill=color,
            anchor="middle", raw=ident_raw),
        txt(cx, cy + 35, SLOT, size=12, family=MONO, fill=GRAY5,
            anchor="middle"),
    ))


def edge_label(cx: float, y0: float, rel: str, mech: str, *,
               color: str = BLACK) -> str:
    """Lowe's relation, and under it the PKC mechanism that *is* that relation."""
    return "".join((
        txt(cx, y0, rel, size=12.5, style="italic", fill=GRAY5, anchor="middle"),
        txt(cx, y0 + 18, mech, size=12.5, fill=color, anchor="middle", raw=True),
    ))


def m_corner_stack() -> str:
    """The M corner, at four carriers. Only this corner is indexed by `R`, so
    only this corner has depth — the other three do not move.

    Every plate is laid down before any plate's label, so a nearer plate can
    never paint over a farther one's name.
    """
    x0, y0 = CXR - CARD_HW, CARD_T
    wd, ht = 2 * CARD_HW, CARD_B - CARD_T
    o: list[str] = []
    for _, i in PLATES:
        o.append(
            f'<rect x="{x0 + i * PLATE_DX:.1f}" y="{y0 + i * PLATE_DY:.1f}" '
            f'width="{wd:.1f}" height="{ht:.1f}" rx="4" fill="#FFFFFF" '
            f'stroke="{GRAY5}" stroke-width="1.1" '
            f'opacity="{1.0 - 0.17 * i:.2f}"/>'
        )
    o.append(f'<rect x="{x0:.1f}" y="{y0:.1f}" width="{wd:.1f}" height="{ht:.1f}" '
             f'rx="4" fill="#FFFFFF" stroke="{BLACK}" stroke-width="1.8"/>')
    for name, i in PLATES:
        o.append(txt(x0 + i * PLATE_DX + wd - 9, y0 + i * PLATE_DY + ht - 7,
                     name, size=11.5, family=MONO, fill=GRAY5, anchor="end"))
    # the three parameters carry the same colors here as on the edges they are:
    # `o` the heavy bottom edge, `k` the red right edge, `R` no edge at all.
    o.append(corner(CXR, CYB, "Modes",
                    f'IndividualQuantity <tspan font-weight="700">o</tspan> '
                    f'<tspan fill="{RED}" font-weight="700">k</tspan> '
                    f'<tspan fill="{GRAY5}" font-weight="700">R</tspan>',
                    ident_raw=True))
    o.append(txt(x0 + wd - 9, CARD_B - 8, "R=Int", size=11.5, family=MONO,
                 fill=BLACK, weight="700", anchor="end"))
    o.append(txt(x0, CARD_B + 3 * PLATE_DY + 22,
                 "indexed by a carrier representation, R", size=12.5,
                 style="italic", fill=GRAY5))
    return "".join(o)


def build() -> str:
    o = [f'<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W:.0f} {H:.0f}" '
         f'font-family="{SANS}">',
         f'<rect width="{W:.0f}" height="{H:.0f}" fill="#FFFFFF"/>',
         scope()]

    o.append(line(338, CYT, 455, CYT))                       # top, K—A
    o.append(line(573, CYT, 700, CYT))
    o.append(edge_label(514, CYT - 5, "characterized by", mono_t("DedicatedKind")))

    o.append(line(CXL, 142, CXL, 170))                       # left, K—S
    o.append(line(CXL, 216, CXL, 246))
    o.append(edge_label(CXL, 189, "instantiated by", mono_t("Sorted.sortOf")))

    o.append(line(338, CYB, 425, CYB, w=THICK))              # bottom, S—M
    o.append(line(557, CYB, CXR - CARD_HW, CYB, w=THICK))
    o.append(edge_label(491, CYB - 13, "characterized by",
                        f'an object index, <tspan font-family="{MONO}" '
                        f'font-weight="700">o</tspan>'))

    o.append(line(CXR, 142, CXR, 170, stroke=RED, w=THICK))  # right, A—M
    o.append(line(CXR, 216, CXR, CARD_T, stroke=RED, w=THICK))
    o.append(edge_label(CXR, 189, "instantiated by",
                        f'a kind index, <tspan font-family="{MONO}" '
                        f'fill="{RED}" font-weight="700">k</tspan>', color=RED))

    dash = "6 5"                                             # diagonal, S—A
    o.append(line(336.1, 243.1, 411.1, 217.1, stroke=GRAY5, w=1.4, dash=dash))
    o.append(line(600.1, 151.5, 675.0, 125.5, stroke=GRAY5, w=1.4, dash=dash))
    o.append(edge_label(505.6, 180, "exemplified by",
                        f'<tspan font-style="italic">derived</tspan> — either '
                        f'path around the square'))

    o.append(corner(CXL, CYT, "Kinds", "SortOfSystem"))
    o.append(corner(CXR, CYT, "Attributes", "KindOfProperty", color=RED))
    o.append(corner(CXL, CYB, "Substances", "o : O"))
    o.append(m_corner_stack())

    # the key for the two heavy strokes — one line, on the figure's bottom rule.
    o.append(line(60, 424, 92, 424, w=THICK))
    o.append(txt(100, 428, "a heavy edge is a type index", size=12.5, fill=GRAY5))

    o.append("</svg>")
    return "".join(o)


def mono_t(s: str) -> str:
    return f'<tspan font-family="{MONO}">{escape(s)}</tspan>'


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--out", default=None)
    args = ap.parse_args()
    out = pathlib.Path(args.out) if args.out else FIGURES / "lowe-square-pkc.svg"
    out.parent.mkdir(parents=True, exist_ok=True)
    out.write_text(build(), encoding="utf-8")
    print(f"{out}  {out.stat().st_size:,} bytes")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
