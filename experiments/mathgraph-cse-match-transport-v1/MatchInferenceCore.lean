/- Consequence-quotiented, proof-carrying classification of candidate PKC matches. -/

module

public import RecordedCseQualification

@[expose] public section Blanket

namespace PropertyKindCalculus.Experiments.MatchInferenceCore

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm

/-- Stable names for every Boolean conjunct in `Match.accepts`, plus the generator boundary. -/
inductive MatchAcceptanceClause where
  | noCandidates
  | tapeOrdered
  | totalOnNodes
  | uniqueKeys
  | keysDeclared
  | componentsDisjoint
  | leavesAreSources
  | sourcesAreLeaves
  | realizedTopology
  | interiorsDisjoint
  | coverage
  | realizesAll
  | realizedInGraph
deriving DecidableEq, Repr, BEq

def MatchAcceptanceClause.label : MatchAcceptanceClause → String
  | .noCandidates => "no-candidates"
  | .tapeOrdered => "tape-ordered"
  | .totalOnNodes => "total-on-nodes"
  | .uniqueKeys => "unique-keys"
  | .keysDeclared => "keys-declared"
  | .componentsDisjoint => "components-disjoint"
  | .leavesAreSources => "leaves-are-sources"
  | .sourcesAreLeaves => "sources-are-leaves"
  | .realizedTopology => "realized-topology"
  | .interiorsDisjoint => "interiors-disjoint"
  | .coverage => "coverage"
  | .realizesAll => "realizes-all"
  | .realizedInGraph => "realized-in-graph"

def failedClause (clause : MatchAcceptanceClause) (ok : Bool) :
    List MatchAcceptanceClause :=
  if ok then [] else [clause]

/-- Complete, stable residual vocabulary for PKC's current acceptance definition. -/
def matchFailures [BEq ν] [BEq κ] (g : Provenance ν κ) (T : TapeGraph)
    (m : Match ν) : List MatchAcceptanceClause :=
  failedClause .tapeOrdered T.ordered ++
  failedClause .totalOnNodes (Match.totalOnNodes g T m) ++
  failedClause .uniqueKeys (Match.uniqueKeys m) ++
  failedClause .keysDeclared (Match.keysDeclared g m) ++
  failedClause .componentsDisjoint (Match.componentsDisjoint m) ++
  failedClause .leavesAreSources (Match.leavesAreSources g T m) ++
  failedClause .sourcesAreLeaves (Match.sourcesAreLeaves g T m) ++
  failedClause .realizedTopology (m.realized.all (Match.realizedOk g T m)) ++
  failedClause .interiorsDisjoint (Match.interiorsDisjoint m) ++
  failedClause .coverage (Match.covering g T m) ++
  failedClause .realizesAll (Match.realizesAll g m) ++
  failedClause .realizedInGraph (Match.realizedInGraph g m)

/-- Canonicalize a vertex set in tape order. -/
def canonicalVertices (T : TapeGraph) (vertices : List Nat) : List Nat :=
  (List.range T.size).filter vertices.contains

def realizationAt? (m : Match ν) (occ : Nat) : Option Realized :=
  m.realized.find? fun r => r.occ == occ

/-- Observable boundary and silent realization attributed to one occurrence. -/
structure OccurrenceConsequences where
  occurrence : Nat
  frontier : List Nat
  roots : List Nat
  interior : List Nat
deriving DecidableEq, Repr, BEq

/-- Everything about a match that PKC's accepted correspondence exposes and protects. -/
structure ProtectedConsequences (ν : Type) where
  componentOwners : List (Option ν)
  occurrences : List OccurrenceConsequences
  operationOwners : List (List Nat)
deriving Repr, BEq

def protectedConsequences [BEq ν] [BEq κ] (g : Provenance ν κ) (T : TapeGraph)
    (m : Match ν) : ProtectedConsequences ν where
  componentOwners := (List.range T.size).map m.nodeOf?
  occurrences := (List.range g.occurrences.length).map fun i =>
    match realizationAt? m i with
    | none => ⟨i, [], [], []⟩
    | some r => ⟨i,
        canonicalVertices T (m.frontier g r),
        canonicalVertices T (m.roots g r),
        canonicalVertices T r.interior⟩
  operationOwners := (List.range T.size).map fun v =>
    if T.isOp v then
      (List.range g.occurrences.length).filter fun i =>
        match realizationAt? m i with
        | none => false
        | some r => (m.body g r).contains v
    else []

def sameProtectedConsequences [BEq ν] [BEq κ] (g : Provenance ν κ)
    (T : TapeGraph) (left right : Match ν) : Bool :=
  protectedConsequences g T left == protectedConsequences g T right

/-- A candidate retained only after the existing PKC checker accepts it. -/
structure AcceptedCandidate [BEq ν] [BEq κ]
    (g : Provenance ν κ) (T : TapeGraph) where
  sourceMatch : Match ν
  accepted : sourceMatch.Accepts g T

def acceptCandidate? [BEq ν] [BEq κ] (g : Provenance ν κ) (T : TapeGraph)
    (m : Match ν) : Option (AcceptedCandidate g T) :=
  match h : m.accepts g T with
  | true => some ⟨m, h⟩
  | false => none

structure ConsequenceClass [BEq ν] [BEq κ]
    (g : Provenance ν κ) (T : TapeGraph) where
  representative : AcceptedCandidate g T
  alternatives : List (AcceptedCandidate g T)

def ConsequenceClass.consequences [BEq ν] [BEq κ]
    {g : Provenance ν κ} {T : TapeGraph} (c : ConsequenceClass g T) :
    ProtectedConsequences ν :=
  protectedConsequences g T c.representative.sourceMatch

def insertAccepted [BEq ν] [BEq κ] {g : Provenance ν κ} {T : TapeGraph}
    (candidate : AcceptedCandidate g T) :
    List (ConsequenceClass g T) → List (ConsequenceClass g T)
  | [] => [⟨candidate, []⟩]
  | cls :: rest =>
      if sameProtectedConsequences g T candidate.sourceMatch cls.representative.sourceMatch then
        { cls with alternatives := candidate :: cls.alternatives } :: rest
      else
        cls :: insertAccepted candidate rest

def consequenceClasses [BEq ν] [BEq κ] {g : Provenance ν κ} {T : TapeGraph}
    (candidates : List (AcceptedCandidate g T)) : List (ConsequenceClass g T) :=
  candidates.foldl (fun classes candidate => insertAccepted candidate classes) []

inductive AmbiguityKind where
  | componentOwnership
  | occurrenceBoundary
  | operationOwnership
deriving DecidableEq, Repr, BEq

structure AmbiguitySeparator where
  kind : AmbiguityKind
  index : Nat
deriving DecidableEq, Repr, BEq

def firstDifference [BEq α] : List α → List α → Nat → Option Nat
  | [], [], _ => none
  | [], _ :: _, i => some i
  | _ :: _, [], i => some i
  | x :: xs, y :: ys, i => if x == y then firstDifference xs ys (i + 1) else some i

def consequenceSeparator [BEq ν] (left right : ProtectedConsequences ν) :
    Option AmbiguitySeparator :=
  match firstDifference left.componentOwners right.componentOwners 0 with
  | some i => some ⟨.componentOwnership, i⟩
  | none =>
      match firstDifference left.occurrences right.occurrences 0 with
      | some i => some ⟨.occurrenceBoundary, i⟩
      | none =>
          (firstDifference left.operationOwners right.operationOwners 0).map fun i =>
            ⟨.operationOwnership, i⟩

/-- A deterministic local witness for why no supplied candidate was admitted. -/
structure MatchObstruction where
  failures : List MatchAcceptanceClause
  vertices : List Nat
  occurrences : List Nat
deriving DecidableEq, Repr, BEq

def localConflict [BEq ν] [BEq κ] (g : Provenance ν κ) (T : TapeGraph)
    (m : Match ν) : MatchObstruction :=
  let unownedLeaves := T.leaves.filter fun v => !m.isComponent v
  let uncoveredOps := T.ops.filter fun v =>
    !m.realized.any fun r => !m.isWire g r && (m.body g r).contains v
  let vertices := if !unownedLeaves.isEmpty then unownedLeaves.take 1 else uncoveredOps.take 1
  ⟨matchFailures g T m, vertices,
    m.realized.filterMap fun r => if r.occ < g.occurrences.length then none else some r.occ⟩

def smallerObstruction (left right : MatchObstruction) : MatchObstruction :=
  if left.vertices.length + left.occurrences.length <=
      right.vertices.length + right.occurrences.length then left else right

def rejectedObstruction [BEq ν] [BEq κ] (g : Provenance ν κ) (T : TapeGraph) :
    List (Match ν) → MatchObstruction
  | [] => ⟨[.noCandidates], [], []⟩
  | first :: rest =>
      rest.foldl (fun best candidate => smallerObstruction best (localConflict g T candidate))
        (localConflict g T first)

inductive MatchInferenceStatus where
  | inferred
  | ambiguous
  | rejected
deriving DecidableEq, Repr, BEq

inductive MatchInferenceOutcome [BEq ν] [BEq κ]
    (g : Provenance ν κ) (T : TapeGraph) where
  | inferred (resultClass : ConsequenceClass g T)
  | ambiguous (classes : List (ConsequenceClass g T))
      (separator : Option AmbiguitySeparator)
  | rejected (obstruction : MatchObstruction)

def MatchInferenceOutcome.status [BEq ν] [BEq κ]
    {g : Provenance ν κ} {T : TapeGraph} : MatchInferenceOutcome g T → MatchInferenceStatus
  | .inferred _ => .inferred
  | .ambiguous _ _ => .ambiguous
  | .rejected _ => .rejected

/-- Admit candidates, quotient harmless authoring differences, and expose protected ambiguity. -/
def classifyCandidates [BEq ν] [BEq κ] (g : Provenance ν κ) (T : TapeGraph)
    (candidates : List (Match ν)) : MatchInferenceOutcome g T :=
  let accepted := candidates.filterMap (acceptCandidate? g T)
  match consequenceClasses accepted with
  | [] => .rejected (rejectedObstruction g T candidates)
  | [one] => .inferred one
  | first :: second :: rest =>
      .ambiguous (first :: second :: rest)
        (consequenceSeparator first.consequences second.consequences)

end PropertyKindCalculus.Experiments.MatchInferenceCore

end Blanket
