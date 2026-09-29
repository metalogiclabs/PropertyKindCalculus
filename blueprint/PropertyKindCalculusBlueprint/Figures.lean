/-
# The hand-authored schematics, inlined (the `svg_figure` directive)

Three figures in this document are schematics rather than harvests: the architecture cake
(the stack a model's trust traces down through), Lowe's square labelled with the calculus's
identifiers, and the three layers a capstone is stated over. Each is emitted as SVG by a
generator under `scripts/figures/` into `figures/`, from where this module reads it at
compile time and `:::svg_figure` inlines it into the page — through the same
`Block.diagram` the Manual genre's `diagram` code block uses for Illuminate drawings, so a
schematic renders exactly as a drawn diagram does: inline in the multi-page and single-page
HTML, and as an `\includesvg` in the LaTeX output.

Why a file and not a drawing: the generators carry raster logos and typographic detail
Illuminate does not express, and the same SVG is committed beside the JPL Gen-AI deck,
which the generator writes with `--out`. Why inline and not an `<img>`: the multi-page site
nests chapters two directories deep, so one relative path cannot resolve on every page,
and the single page has no directory at all.

`include_str` reads a figure when *this* module compiles, and Lake's trace does not see the
file: regenerating a figure does not rebuild this module on its own, which is why
`scripts/make-figures.sh` removes this module's build products after writing a changed
figure, and why `scripts/ci-pages.sh` runs `make-figures.sh --check` before a render.
-/

import VersoManual
import VersoBlueprint

open Lean Elab
open Verso Doc Elab ArgParse
open Verso.Genre.Manual

namespace PropertyKindCalculusBlueprint

/-! ## The figures, as strings -/

namespace Figures

/-- The architecture cake, blueprint audience: `scripts/figures/make-architecture-cake.py`. -/
def architectureCake : String := include_str "../figures/architecture-cake.svg"

/-- Lowe's square with the calculus's identifiers: `scripts/figures/make-lowe-square-pkc.py`. -/
def loweSquare : String := include_str "../figures/lowe-square-pkc.svg"

/-- The three layers and their two ladders: `scripts/figures/make-three-layers-pkc.py`. -/
def threeLayers : String := include_str "../figures/three-layers-pkc.svg"

end Figures

/-! ## The directive -/

structure FigureConfig where
  /-- The name of the `String` constant holding the SVG. -/
  figure : Ident
  /-- The CSS width of the inlined figure; `100%` when omitted. -/
  cssWidth : Option String
  /-- The LaTeX width of the included figure; `\textwidth` when omitted. -/
  texWidth : Option String

section
variable [Monad m] [MonadError m] [MonadInfoTree m] [MonadLiftT CoreM m] [MonadEnv m]
  [MonadFileMap m]

def FigureConfig.parse : ArgParse m FigureConfig :=
  FigureConfig.mk <$> .positional `figure ValDesc.ident
    <*> .named' `cssWidth true
    <*> .named' `texWidth true

instance : FromArgs FigureConfig m := ⟨FigureConfig.parse⟩
end

unsafe def evalSvgUnsafe (stx : Syntax) : TermElabM String :=
  Term.evalTerm String (mkConst ``String) stx

@[implemented_by evalSvgUnsafe]
opaque evalSvg (stx : Syntax) : TermElabM String

/-- `:::svg_figure PropertyKindCalculusBlueprint.Figures.threeLayers` inlines the SVG the
named `String` constant holds, as a `Block.diagram`. Optional `(cssWidth := "…")` and
`(texWidth := "…")` as for the `diagram` code block. Contents are ignored. -/
@[directive]
def svg_figure : DirectiveExpanderOf FigureConfig
  | cfg, _contents => do
    let svg ← evalSvg cfg.figure
    let css := cfg.cssWidth.getD "100%"
    let tex := cfg.texWidth.getD "\\textwidth"
    ``(Verso.Doc.Block.other
        (Verso.Genre.Manual.Block.diagram $(quote svg) $(quote css) $(quote tex) false) #[])

end PropertyKindCalculusBlueprint
