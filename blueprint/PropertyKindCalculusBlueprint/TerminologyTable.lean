/-
# The `terminology_dictionary` directive — the dictionary, rendered from the data

`:::terminology_dictionary` expands into the terminological dictionary as a table, read from
`PropertyKindCalculus.Terminology.dictionary`, sorted by canonical phrase. Each row carries the
term with its sanctioned short form, its gloss, the declarations that carry the concept, the
retired phrasings the gate refuses, and a link to the section that defines the term — the one
section holding its `{deftech}`, which is where the explaining prose lives.

Rendering is where two checks fire. Every declaration a term cites is looked up in the
environment the blueprint is built against, so a renamed declaration reaches the document as a
build failure rather than as a stale name in a table. And the count sentence
(`:::terminology_count`) is computed, so a chapter cannot report a dictionary size the data
does not have.
-/

import VersoManual
import VersoBlueprint
import PropertyKindCalculus.Terminology
import PropertyKindCalculusBlueprint.ItemIndex

open Lean Elab
open Verso Doc Elab
open Verso.Genre Manual
open Verso.ArgParse
open PropertyKindCalculus.Terminology
open PropertyKindCalculusBlueprint.ItemIndex

namespace PropertyKindCalculusBlueprint.TerminologyTable

/-- The directives take no arguments: the dictionary is one object. -/
structure Config where

section
variable [Monad m]
instance : FromArgs Config m := ⟨pure {}⟩
end

/-- Every declaration a term cites must exist in the environment the blueprint is built
against — a renamed declaration then reaches the document as a build failure, the same way a
dangling section tag does. -/
def checkDecls : DocElabM Unit := do
  let env ← getEnv
  for t in dictionary do
    for n in t.decls do
      unless env.contains n do
        throwError "terminology: term '{t.key}' cites `{n}`, which is not a declaration in \
                    this environment"

/-- The entries by canonical phrase. -/
def sorted : List PropertyKindCalculus.Terminology.Term :=
  (dictionary.toArray.qsort (fun a b => decide (a.key < b.key))).toList

/-- The term cell: the canonical phrase, and the short form when one is sanctioned. -/
def termCell (t : PropertyKindCalculus.Terminology.Term) : Cell :=
  match t.short with
  | some s => .md s!"**{t.key}** — short form *{s}*"
  | none => .md s!"**{t.key}**"

/-- The declarations, as inline code; an em dash where a term names none. -/
def declsCell (t : PropertyKindCalculus.Terminology.Term) : Cell :=
  if t.decls.isEmpty then .text "—" else .links (t.decls.map fun n => ("", n.toString))

/-- The retired phrasings, or an em dash where none is recorded. -/
def avoidCell (t : PropertyKindCalculus.Terminology.Term) : Cell :=
  if t.avoid.isEmpty then .text "—"
  else .md (String.intercalate ", " (t.avoid.map fun a => s!"*{a}*"))

/-- The dictionary as a `DocTable`. -/
def buildTable : DocTable :=
  { headers := ["Term", "Meaning", "Declarations", "Retired phrasings", "Defined in"],
    rows := sorted.map fun t =>
      [ termCell t, .md t.gloss, declsCell t, avoidCell t, .secref t.definedIn t.definedIn ] }

@[directive]
def terminology_dictionary : DirectiveExpanderOf Config
  | _cfg, _contents => do
    checkDecls
    docTableTerm buildTable

/-- The count sentence, *computed* — so the chapter cannot report a size the data does not
have. -/
def countSentence : String :=
  let n := dictionary.length
  let withShort := (dictionary.filter (·.short.isSome)).length
  let withAvoid := (dictionary.filter (!·.avoid.isEmpty)).length
  let cited := dictionary.foldl (fun acc t => acc + t.decls.length) 0
  s!"The dictionary carries {n} terms: {withShort} with a sanctioned short form, {withAvoid} \
     with retired phrasings the gate refuses, and {cited} declaration citations that the \
     blueprint build checks exist."

@[directive]
def terminology_count : DirectiveExpanderOf Config
  | _cfg, _contents => do
    cellBlock (.md countSentence)

end PropertyKindCalculusBlueprint.TerminologyTable
