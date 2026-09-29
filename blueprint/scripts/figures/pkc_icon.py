"""The PropertyKindCalculus mark, wordless — Lowe's square reduced to an icon.

It is the explanatory figure (`make-lowe-square-pkc.py`) with every word taken
out, so that a viewer who has seen that slide recognizes the band on the
architecture cake at a glance, and a viewer who has not still sees a square with
one corner emphasized and one corner stacked.

What survives the reduction is exactly what the figure's geometry asserts, and
nothing that only its labels asserted:

  · four corner nodes — the square's four categories, in Lowe's arrangement,
    universals above and particulars below, substantial left and
    non-substantial right;
  · the Attributes node in red — the corner the library is named for, and the
    `k` of `Quantity k R`;
  · two heavy edges meeting at Modes, drawn at three times the weight of the
    other two, because those two are the ones carried in the type of an
    individual quantity: the object index along the bottom and the kind index
    down the right;
  · the diagonal dashed, because exemplification is derived rather than
    primitive — it factors through either path around the square;
  · plates behind Modes — the carrier. `R` is not an ontological category, has
    neither a corner nor an edge, and indexes only that one corner, so it
    stacks copies of the mode instead of moving anything.

Sources, all in PropertyKindCalculus:
  corners, edges   `blueprint/…/Chapters/Foundations.lean` 141–151, including
                   "both edges into the mode are carried in the *type* of an
                   individual quantity".
  the diagonal     same file, 153–162 — "factoring through either path around
                   the square".
  the signature    `IndividualQuantity.lean` 73.

The icon is drawn about its square, but its plates extend down and to the right,
so `extent()` reports the real bounding box for a caller that needs to center it
in a slot.
"""

from __future__ import annotations

RED = "#E4002B"
BLACK = "#000000"
GRAY5 = "#767676"

NODE_R = 0.085      # corner node radius, as a fraction of the side
PLATE = 0.32        # the Modes plate, likewise
PLATE_STEP = 0.05   # how far each plate behind it recedes, down and right
GAP = 0.17          # how far an edge stops short of a corner node


def extent(s: float) -> tuple[float, float, float, float]:
    """(left, top, right, bottom) of the drawn mark, relative to its center.

    Not symmetric: the plates hang below and to the right of the square, so a
    caller that centers the square centers the wrong thing.
    """
    front, back = 0.5 + NODE_R, 0.5 + PLATE / 2 + 3 * PLATE_STEP
    return (-s * front, -s * front, s * back, s * back)


def icon(cx: float, cy: float, s: float, *, red: str = RED, black: str = BLACK,
         gray: str = GRAY5) -> str:
    """The wordless mark, its square of side `s` centered on (cx, cy)."""
    half = s / 2.0
    xl, xr, yt, yb = cx - half, cx + half, cy - half, cy + half
    r = s * NODE_R
    side = s * PLATE
    gap = s * GAP
    gap_m = side / 2 + s * 0.03          # edges stop at the plate, not the node
    thin = max(0.9, s * 0.035)
    thick = thin * 3.0                    # a type index, at three times the weight
    o: list[str] = []

    # the carrier: plates behind Modes, farthest first
    for i in (3, 2, 1):
        d = i * s * PLATE_STEP
        o.append(
            f'<rect x="{xr - side / 2 + d:.2f}" y="{yb - side / 2 + d:.2f}" '
            f'width="{side:.2f}" height="{side:.2f}" rx="{s * 0.035:.2f}" '
            f'fill="#FFFFFF" stroke="{gray}" stroke-width="{thin * 0.8:.2f}" '
            f'opacity="{1.0 - 0.18 * i:.2f}"/>'
        )

    # the two ordinary edges — characterization across the top, instantiation
    # down the left
    o.append(f'<line x1="{xl + gap:.2f}" y1="{yt:.2f}" x2="{xr - gap:.2f}" '
             f'y2="{yt:.2f}" stroke="{black}" stroke-width="{thin:.2f}"/>')
    o.append(f'<line x1="{xl:.2f}" y1="{yt + gap:.2f}" x2="{xl:.2f}" '
             f'y2="{yb - gap:.2f}" stroke="{black}" stroke-width="{thin:.2f}"/>')

    # the two type indices — the object along the bottom, the kind down the right
    o.append(f'<line x1="{xl + gap:.2f}" y1="{yb:.2f}" x2="{xr - gap_m:.2f}" '
             f'y2="{yb:.2f}" stroke="{black}" stroke-width="{thick:.2f}"/>')
    o.append(f'<line x1="{xr:.2f}" y1="{yt + gap:.2f}" x2="{xr:.2f}" '
             f'y2="{yb - gap_m:.2f}" stroke="{red}" stroke-width="{thick:.2f}"/>')

    # exemplification: derived, so dashed, and it touches neither type index
    g = gap * 0.85
    o.append(f'<line x1="{xl + g:.2f}" y1="{yb - g:.2f}" x2="{xr - g:.2f}" '
             f'y2="{yt + g:.2f}" stroke="{gray}" stroke-width="{thin * 0.9:.2f}" '
             f'stroke-dasharray="{s * 0.07:.2f} {s * 0.055:.2f}"/>')

    # the front plate is the Modes corner itself, so it is drawn solid and last
    o.append(
        f'<rect x="{xr - side / 2:.2f}" y="{yb - side / 2:.2f}" '
        f'width="{side:.2f}" height="{side:.2f}" rx="{s * 0.035:.2f}" '
        f'fill="#FFFFFF" stroke="{black}" stroke-width="{thin * 1.4:.2f}"/>'
    )
    for x, y, col in ((xl, yt, black), (xr, yt, red), (xl, yb, black)):
        o.append(f'<circle cx="{x:.2f}" cy="{y:.2f}" r="{r:.2f}" fill="{col}"/>')
    return "".join(o)
