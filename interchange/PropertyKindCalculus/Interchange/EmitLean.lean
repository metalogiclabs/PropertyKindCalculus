/-
# `EmitLean` — print a `PkcModel` as a Lean module the kernel re-checks

The last step of the SysML → Lean half. A model read from the DSL becomes an ordinary Lean
module of the calculus: `ExaminationPrinciple` and `KindOfProperty` definitions, one `Edge`
inductive for the declared specializations, `KindMul`/`KindDiv` instances for the table edges
and `ProductKind`/`QuotientKind` theorems for the authored ones (each discharged by the
calculus's smart constructors, so the ratio-scale gate is *checked*, not copied), the
boundaries as `Provenance.Contract String String` values with their relations and
requirements, and the tapes as `Paradigm.TapeGraph` values with their ordering decided.

What the SysML author asserted beyond this — a `@Checked` citation — is not restated as a
theorem: a citation names a declaration the importer verifies exists; the generated module
records it in a comment beside the element. The module is what `lake build` then accepts or
refuses, which is how a SysML model receives the calculus's verdicts.
-/

module

public import PropertyKindCalculus.Interchange.Model

@[expose] public section Blanket

namespace PropertyKindCalculus.Interchange.EmitLean

open PropertyKindCalculus.Interchange

/-- A Lean identifier for an element name: letters, digits and `_` kept, everything else
replaced by `_`; a leading digit prefixed. -/
def ident (s : String) : String :=
  let core := s.map fun c => if c.isAlphanum || c == '_' then c else '_'
  let core := if core.isEmpty then "_" else core
  if core.front.isDigit then "_" ++ core else core

/-- A Lean string literal. -/
def str (s : String) : String :=
  "\"" ++ (s.foldl (fun acc c =>
    if c == '"' then acc ++ "\\\"" else if c == '\\' then acc ++ "\\\\"
    else if c == '\n' then acc ++ "\\n" else acc.push c) "") ++ "\""

def optStr : Option String → String
  | some s => s!"some {str s}"
  | none => "none"

def strList (ss : List String) : String := "[" ++ String.intercalate ", " (ss.map str) ++ "]"

def nameList (ss : List String) : String := "[" ++ String.intercalate ", " (ss.map ("`" ++ ·)) ++ "]"

/-- A `Lean.Name` literal, `.anonymous` for none. -/
def nameLit : Option String → String
  | some s => if s.isEmpty then ".anonymous" else "`" ++ s
  | none => ".anonymous"

def natList (ns : List Nat) : String := "[" ++ String.intercalate ", " (ns.map toString) ++ "]"

def scaleCtor : Scale → String
  | .nominal => ".nominal" | .ordinal => ".ordinal" | .interval => ".interval" | .ratio => ".ratio"

def dirCtor : PortDir → String
  | .input => ".input" | .config => ".config" | .param => ".param" | .output => ".output"
  | .conditional => ".conditional"

def roleCtor : BoundaryRole → String
  | .model => ".model" | .specification => ".specification"

def relationCtor : RelationKind → String
  | .inverts => ".inverts" | .refines => ".refines" | .equals => ".equals" | .boundedBy => ".boundedBy"

def transferCtor (l : License) : String :=
  match l.transfer with
  | .exact => ".exact `" ++ l.witness | .nonneg => ".nonneg `" ++ l.witness
  | .restated => ".restated `" ++ l.witness

def requirementCtor : RequirementKind → String
  | .provable => ".provable" | .empirical => ".empirical"

/-- The `RequirementScope` a pivot scope string denotes (the harvester's rendering:
`sort N`, `objects A, B`, `decided D`); absent or unrecognized is `.all`. -/
def scopeCtor : Option String → String
  | some s =>
    if s.startsWith "sort " then ".sort " ++ nameLit (some (s.drop 5).toString)
    else if s.startsWith "decided " then ".decided " ++ nameLit (some (s.drop 8).toString)
    else if s.startsWith "objects " then
      ".objects " ++ nameList ((s.drop 8).toString.splitOn ", ")
    else ".all"
  | none => ".all"

/-- Text destined for a comment: one line, with no comment terminator in it — a model is
input, not code, and must not be able to end its comment and start a command. -/
def commentText (s : String) : String :=
  (s.map fun c => if c == '\n' || c == '\r' then ' ' else c).replace "-/" "- /"

def citationComment (source : Option String) (checked : List Checked) : List String :=
  (source.map fun s => s!"-- source: {commentText s}").toList
    ++ checked.map fun c =>
      s!"-- checked: {commentText c.decl}" ++ (c.statement.map (s!" — {commentText ·}")).getD ""

/-- The module's principle definitions. -/
def principles (m : PkcModel) : List String :=
  m.principles.flatMap fun p =>
    citationComment p.source [] ++
    [s!"def {ident p.name} : ExaminationPrinciple := \{ id := {str p.id} }", ""]

/-- The module's kind definitions — `KindOfProperty` values; the dimension vector and the
catalogue locators ride along as documentation, the dimension layer being PhysLib-backed. -/
def kinds (m : PkcModel) : List String :=
  m.kinds.flatMap fun k =>
    let principleId := k.principle.bind fun pn => (m.principles.find? (·.name == pn)).map (·.id)
    let doc := [k.standardRef.map (s!"standard: {·}"), k.catalogueItem.map (s!"item: {·}"),
                k.symbol.map (s!"symbol: {·}"), k.coherentUnit.map (s!"coherent unit: {·}"),
                if k.dimension.isEmpty then none else
                  some ("dimension: " ++ String.intercalate " · " (k.dimension.map fun d =>
                    s!"{d.base}^{if d.den == 1 then toString d.num else s!"({d.num}/{d.den})"}"))].filterMap id
    citationComment k.source k.checked ++
    (if doc.isEmpty then [] else [s!"/-- {commentText (String.intercalate "; " doc)} -/"]) ++
    [s!"def {ident k.name} : KindOfProperty :=",
     s!"  \{ id := {str k.id}, scale := {scaleCtor k.scale}, examPrinciple := {optStr principleId} }", ""]

/-- The specialization relation, one constructor per declared edge. -/
def specialization (m : PkcModel) : List String :=
  let ctors := m.kinds.flatMap fun k => k.specializes.map fun g =>
    s!"  | {ident k.name}_{ident g} : Edge {ident k.name} {ident g}"
  if ctors.isEmpty then [] else
  ["/-- The declared specializations: `Specializes Edge` is their transitive closure. -/",
   "inductive Edge : KindOfProperty → KindOfProperty → Prop"] ++ ctors ++ [""]

/-- The kind algebra: table edges as instances, authored product/quotient laws as theorems,
both built by the smart constructors whose ratio-scale gates `rfl` decides. Other families
are recorded for the reader — their laws need the witness the citation names. -/
def algebra (m : PkcModel) : List String :=
  m.edges.flatMap fun e =>
    let ks := e.operands ++ e.result.toList |>.map ident
    let args := String.intercalate " " ks
    citationComment e.source e.checked ++
    (match e.kind, e.table, ks.length with
    | .product, true, 3 => [s!"instance : KindMul {args} := ⟨ProductKind.ofRatio {args}⟩"]
    | .quotient, true, 3 => [s!"instance : KindDiv {args} := ⟨QuotientKind.ofRatio {args}⟩"]
    | .product, false, 3 => [s!"theorem {ident e.name} : ProductKind {args} := ProductKind.ofRatio {args}"]
    | .quotient, false, 3 => [s!"theorem {ident e.name} : QuotientKind {args} := QuotientKind.ofRatio {args}"]
    | k, _, _ => [commentText s!"-- {repr k} edge {e.name}: {args} (witness required; not generated)"]) ++ [""]

def dedicated (m : PkcModel) : List String :=
  m.dedicated.flatMap fun d =>
    citationComment d.source [] ++
    [s!"def {ident d.name} : DedicatedKind :=",
     s!"  \{ sort := \{ id := {str d.sort} }, component := \{ id := {str d.component} }, kind := {ident d.kind} }", ""]

def units (m : PkcModel) : List String :=
  m.units.flatMap fun u =>
    citationComment u.source [] ++
    [s!"def {ident u.name} : MetrologicalUnit := \{ kind := {ident u.kind}, symbol := {str u.symbol} }", ""]

/-- The boundaries, over `String` nodes and kind names — the declared signature as data. -/
def modules (m : PkcModel) : List String :=
  m.modules.flatMap fun b =>
    let ports := b.ports.map fun p => s!"⟨{str p.node}, {str p.kind}, {dirCtor p.dir}⟩"
    citationComment b.source b.checked ++
    [s!"def {ident b.name} : Provenance.Contract String String where",
     s!"  name := {str b.title}",
     s!"  members := {nameList b.members}",
     s!"  ports := [{String.intercalate ", " ports}]",
     s!"  exits := {strList b.exits}",
     s!"  deciders := [{String.intercalate ", " (b.deciders.map fun (n, d) => s!"({str n}, " ++ "`" ++ d ++ ")")}]",
     s!"  suppliers := [{String.intercalate ", " (b.suppliers.map fun (n, d) => s!"({str n}, " ++ "`" ++ d ++ ")")}]",
     s!"  role := {roleCtor b.role}", ""]

def relations (m : PkcModel) : List String :=
  m.relations.flatMap fun r =>
    citationComment r.source [] ++
    [s!"def {ident r.name} : Provenance.Relation where",
     s!"  left := {nameLit (some r.left)}", s!"  right := {nameLit (some r.right)}", s!"  kind := {relationCtor r.kind}",
     s!"  witness := {nameLit (some r.witness)}", s!"  claim := {str (r.claim.getD "")}",
     s!"  tolerance := {nameLit r.tolerance}", s!"  hypotheses := {nameList r.hypotheses}",
     s!"  licenses := [{String.intercalate ", " (r.licenses.map fun l => s!"⟨{str l.rung}, {transferCtor l}⟩")}]",
     s!"  wellPosed := {nameLit r.wellPosed}", s!"  domain := {nameLit r.domain}",
     s!"  ambiguity := {nameLit r.ambiguity}", ""]

def requirements (m : PkcModel) : List String :=
  m.requirements.flatMap fun r =>
    citationComment r.source [] ++
    (r.port.map fun p => s!"-- port: {commentText p} (a rendered NodeId; not rebuilt)").toList ++
    [s!"def {ident r.name} : Provenance.Requirement where",
     s!"  name := {str r.title}", s!"  statement := {str r.statement}",
     s!"  kind := {requirementCtor r.kind}", s!"  governs := {nameLit (some r.governs)}",
     s!"  scope := {scopeCtor r.scope}",
     s!"  witness := {nameLit r.witness}", s!"  spotChecks := {nameList r.spotChecks}",
     s!"  absent := {nameLit r.absent}", s!"  referents := {nameList r.referents}", ""]

/-- The tapes, each with its build-order invariant decided by the kernel. -/
def tapes (m : PkcModel) : List String :=
  m.tapes.flatMap fun t =>
    let vs := t.vertices.map fun v => s!"⟨{optStr v.name}, {natList v.parents}⟩"
    citationComment t.source t.checked ++
    [s!"def {ident t.name} : Paradigm.TapeGraph := \{ vertices := [{String.intercalate ", " vs}] }",
     s!"example : ({ident t.name}).ordered = true := by decide", ""]

def tapeMatches (m : PkcModel) : List String :=
  m.tapeMatches.flatMap fun x =>
    citationComment x.source x.checked ++
    [commentText (s!"/-- match {x.name}: module `{x.moduleName}` realized on tape `{x.tape}`" ++
       (x.carrier.map fun c => s!" at rung {c.rung}" ++ (c.platform.map (s!" on {·}")).getD "").getD "") ++ " -/",
     s!"def {ident x.name} : Paradigm.Match String :=",
     s!"  \{ components := [{String.intercalate ", " (x.components.map fun c => s!"({str c.node}, {natList c.vertices})")}],",
     s!"    realized := [{String.intercalate ", " (x.realized.map fun r => s!"⟨{r.occ}, {natList r.interior}⟩")}] }", ""]

/-- The whole module. `moduleName` is the Lean module the text is written as. -/
def emit (m : PkcModel) (moduleName : String := s!"Generated.{ident m.packageName}") : String :=
  let header := [
    "module",
    "",
    "public import PropertyKindCalculus",
    "public import PropertyKindCalculus.Paradigm.TapeGraph",
    "",
    s!"/-! # `{moduleName}` — generated from the SysML v2 PKC model `{m.packageName}`",
    "",
    "Written by `PropertyKindCalculus.Interchange.EmitLean`; the kernel's acceptance of this module is",
    "the calculus's verdict on the model. Do not edit — re-import the model instead. -/",
    "",
    "@[expose] public section Blanket",
    "",
    s!"namespace {ident m.packageName}",
    "",
    "open PropertyKindCalculus",
    ""]
  let body := principles m ++ kinds m ++ specialization m ++ algebra m ++ dedicated m ++ units m
    ++ modules m ++ relations m ++ requirements m ++ tapes m ++ tapeMatches m
  let footer := [s!"end {ident m.packageName}", "", "end Blanket", ""]
  String.intercalate "\n" (header ++ body ++ footer)

end PropertyKindCalculus.Interchange.EmitLean

end Blanket
