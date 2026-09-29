/-
# The computational tape graph, and the match that ties it to a provenance hypergraph

A module written once against the branchless carrier class records, when instantiated at
the recording carrier (`Torch.Paradigm.TapeCarrier`), a *tape*: automatic differentiation's
record of the operations it performs, one node per operation with the ids of its parents in
operand order. The **computational tape graph** is the directed acyclic graph that record
determines once each node's value and backward rule are forgotten — one vertex per node, an
edge from each parent to its node, the in-edges of a vertex ordered as its parents are. Its
leaves are of two sorts, a named input and an unnamed constant; every other vertex is an
operation; and it carries no kinds, since a value of any kind records the same node.

This module states that graph as prelude-only data (`TapeGraph`), and beside it the
**match** (`Match`) between a provenance hypergraph and a tape graph that the capstone
chapter's kind-transporting weak bisimulation is read off:

  * a *component table* — for each node of the hypergraph, the tape vertices that realize
    it. One vertex for a real carrier; two for a complex one, the real and imaginary
    parts; several for a bundled carrier. Ports are matched by name and constants by
    recording site, so two constants of one value stay two leaves;
  * a *realization* per occurrence — the occurrence's index and the *interior* vertices of
    the tape sub-graph realizing it. The sub-graph's roots are the components of the
    occurrence's result and its frontier the components of its operands, both read off the
    component table; a realization with no interior whose result shares its operand's
    components is a *wire*, the identity the harvest records as `copy` and the licensed
    re-typing a `step` records.

`Match.accepts` is the decidable acceptance judgment — what a matcher decides and a kernel
theorem pins — and every clause of it is a hypothesis some proof in `Graph.Bisimulation`
consumes: the component table is total on the hypergraph's nodes and injective on the
tape's vertices; every leaf is a component of a source and every source's components are
leaves; every non-wire realization is *closed* (every parent of a sub-graph vertex is an
interior vertex or a frontier vertex), *interior-private* (every edge leaving an interior
vertex stays inside the sub-graph), *progressing* (every interior vertex feeds the
sub-graph, so it lies on a path to a root) and *used* (every frontier vertex feeds the
sub-graph); interiors are pairwise disjoint and disjoint from every component; every
operation vertex lies in some non-wire realization; and the realizations and the
hypergraph's occurrences correspond one to one. Under acceptance the relation "node to its
components" is a strong bisimulation between the hypergraph and the contracted tape graph,
the contraction is a weak bisimulation between the contracted and the actual tape graph,
and their composite is the kind-transporting weak bisimulation (`Graph.Bisimulation`).

Nothing here is specific to TorchLean: the tape library projects its own tape onto this
graph (`Torch.Paradigm.TapeSeal.ofTape`), and an authored graph serves a probe.
-/

module

public import PropertyKindCalculus.Provenance

@[expose] public section Blanket

namespace PropertyKindCalculus.Paradigm

open PropertyKindCalculus.Provenance (Occurrence EdgeFamily)

/-! ## The computational tape graph -/

/-- One vertex of a computational tape graph: what a tape node carries once its value and
its backward rule are forgotten — its name and its parents, in operand order. A leaf (no
parents) is a named input, or an unnamed baked constant; an operation vertex's name is its
operation. -/
structure TapeVertex where
  /-- The input's name, the operation's name, or `none` for a baked constant. -/
  name : Option String
  /-- The parent vertices, in operand order; empty for a leaf. -/
  parents : List Nat
deriving DecidableEq, Repr, Inhabited, BEq

/-- **The computational tape graph**: the directed acyclic graph a tape determines. One
vertex per tape node, in tape order, so a vertex is its index; an edge from each parent to
its vertex. `ordered` is the tape's build invariant — every parent precedes its vertex —
under which the graph is acyclic. -/
structure TapeGraph where
  /-- The vertices, in tape order; a vertex id is its index here. -/
  vertices : List TapeVertex
deriving DecidableEq, Repr, Inhabited, BEq

namespace TapeGraph

/-- The number of vertices. -/
def size (T : TapeGraph) : Nat := T.vertices.length

/-- The vertex at an id, if in range. -/
def vertex? (T : TapeGraph) (v : Nat) : Option TapeVertex := T.vertices[v]?

/-- The parents of a vertex, in operand order; empty out of range. -/
def parents (T : TapeGraph) (v : Nat) : List Nat :=
  match T.vertex? v with
  | some x => x.parents
  | none => []

/-- The name of a vertex: the input's name or the operation's; `none` for a constant leaf
or out of range. -/
def name? (T : TapeGraph) (v : Nat) : Option String :=
  match T.vertex? v with
  | some x => x.name
  | none => none

/-- An edge `u → v`: `u` is a parent of `v`. -/
def edge (T : TapeGraph) (u v : Nat) : Bool := (T.parents v).contains u

/-- A leaf: in range, with no parents. -/
def isLeaf (T : TapeGraph) (v : Nat) : Bool := v < T.size && (T.parents v).isEmpty

/-- An operation vertex: in range, with a parent. -/
def isOp (T : TapeGraph) (v : Nat) : Bool := v < T.size && !(T.parents v).isEmpty

/-- The leaves, in tape order. -/
def leaves (T : TapeGraph) : List Nat := (List.range T.size).filter T.isLeaf

/-- The operation vertices, in tape order. -/
def ops (T : TapeGraph) : List Nat := (List.range T.size).filter T.isOp

/-- The tape's build invariant: every parent precedes its vertex, so the graph is acyclic
and an evaluator walking the vertices in order finds every parent's value already
established. -/
def ordered (T : TapeGraph) : Bool :=
  (List.range T.size).all fun v => (T.parents v).all (· < v)

end TapeGraph

/-! ## The match -/

/-- One realized occurrence: the index of the occurrence in the hypergraph's occurrence
list, and the interior vertices of the tape sub-graph realizing it. The sub-graph's roots
are the components of the occurrence's result and its frontier the components of its
operands (`Match.roots`, `Match.frontier`); an empty interior with the result's components
those of its one operand is a wire (`Match.isWire`). -/
structure Realized where
  /-- The occurrence's index in `Provenance.occurrences`. -/
  occ : Nat
  /-- The interior vertices — the carrier-level expansion the bisimulation is silent on. -/
  interior : List Nat
deriving DecidableEq, Repr, Inhabited, BEq

/-- **A match** between a provenance hypergraph and a computational tape graph: the
component table — each hypergraph node with the tape vertices realizing it — and one
realization per occurrence. The relation the kind-transporting weak bisimulation is read
off; `accepts` is the judgment under which it is one. -/
structure Match (ν : Type) where
  /-- Each node with its component vertices, in a fixed order. -/
  components : List (ν × List Nat)
  /-- The realized occurrences. -/
  realized : List Realized
deriving Repr, Inhabited, BEq

namespace Match

variable {ν κ : Type} [BEq ν] [BEq κ]

/-- The components of a node; empty for a node the table does not carry. -/
def comps (m : Match ν) (n : ν) : List Nat :=
  match m.components.find? (·.1 == n) with
  | some e => e.2
  | none => []

/-- Is a vertex a component of some node — an observable vertex? -/
def isComponent (m : Match ν) (v : Nat) : Bool := m.components.any (·.2.contains v)

/-- The node a vertex is a component of, if any — under acceptance, at most one. -/
def nodeOf? (m : Match ν) (v : Nat) : Option ν :=
  (m.components.find? (·.2.contains v)).map (·.1)

/-- The occurrence a realization realizes. -/
def occOf (g : Provenance ν κ) (r : Realized) : Option (Occurrence ν κ) :=
  g.occurrences[r.occ]?

/-- The operand of a realized occurrence at a position. -/
def operandAt (g : Provenance ν κ) (r : Realized) (i : Nat) : Option ν :=
  match occOf g r with
  | some o => (o.operands[i]?).map (·.1)
  | none => none

/-- The components of the operand at a position: the sub-graph's frontier at that
position. -/
def frontierAt (g : Provenance ν κ) (m : Match ν) (r : Realized) (i : Nat) :
    List Nat :=
  match operandAt g r i with
  | some a => m.comps a
  | none => []

/-- The whole frontier: the components of every operand, in operand order. -/
def frontier (g : Provenance ν κ) (m : Match ν) (r : Realized) : List Nat :=
  match occOf g r with
  | some o => o.operands.flatMap fun oc => m.comps oc.1
  | none => []

/-- The roots: the components of the result. -/
def roots (g : Provenance ν κ) (m : Match ν) (r : Realized) : List Nat :=
  match occOf g r with
  | some o => m.comps o.result
  | none => []

/-- The sub-graph a realization names: its interior and its roots. -/
def body (g : Provenance ν κ) (m : Match ν) (r : Realized) : List Nat :=
  r.interior ++ m.roots g r

/-- The edge family of a realized occurrence. -/
def familyOf (g : Provenance ν κ) (r : Realized) : Option EdgeFamily :=
  (occOf g r).map (·.family)

/-- A wire: no interior, one operand, and the result's components are the operand's. The
identity the harvest records as `copy`, and the licensed re-typing a `step` records. -/
def isWire (g : Provenance ν κ) (m : Match ν) (r : Realized) : Bool :=
  r.interior.isEmpty &&
    match occOf g r with
    | some o =>
      match o.operands with
      | [oc] =>
        (m.comps oc.1).all (m.comps o.result).contains
          && (m.comps o.result).all (m.comps oc.1).contains
      | _ => false
    | none => false

/-- The kind a tape vertex carries by transport: the declared kind of the node it is a
component of. `none` on the interior, where the bisimulation is silent. -/
def kindAt (g : Provenance ν κ) (m : Match ν) (v : Nat) : Option κ :=
  (m.nodeOf? v).bind g.kindOf?

/-! ### The acceptance clauses -/

/-- The declared nodes of a hypergraph: its ports and its introductions. -/
def nodesOf (g : Provenance ν κ) : List ν :=
  g.ports.map (·.node) ++ g.intros.map (·.node)

/-- Every declared node has a component, and every component is a vertex. -/
def totalOnNodes (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) : Bool :=
  (nodesOf g).all fun n => !(m.comps n).isEmpty && (m.comps n).all (· < T.size)

/-- The table names each node once. -/
def uniqueKeys (m : Match ν) : Bool :=
  let ks := m.components.map (·.1)
  ks.all fun n => (ks.filter (· == n)).length == 1

/-- The table names only declared nodes. -/
def keysDeclared (g : Provenance ν κ) (m : Match ν) : Bool :=
  m.components.all fun e => (nodesOf g).contains e.1

/-- No vertex is a component of two nodes. -/
def componentsDisjoint (m : Match ν) : Bool :=
  m.components.all fun e => e.2.all fun v =>
    (m.components.filter (·.2.contains v)).length == 1

/-- Every leaf is a component of a source: a named input of a source port, a constant of a
constant mint or a gated ingest. -/
def leavesAreSources (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) : Bool :=
  T.leaves.all fun v => g.sources.any fun s => (m.comps s).contains v

/-- Every source's components are leaves. -/
def sourcesAreLeaves (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) : Bool :=
  g.sources.all fun s => (m.comps s).all T.isLeaf

/-- Closed: every parent of a sub-graph vertex is an interior vertex or a frontier vertex. -/
def realizedClosed (g : Provenance ν κ) (T : TapeGraph) (m : Match ν)
    (r : Realized) : Bool :=
  (m.body g r).all fun w => (T.parents w).all fun p =>
    r.interior.contains p || (m.frontier g r).contains p

/-- Interior-private: every edge leaving an interior vertex stays inside the sub-graph. -/
def interiorPrivate (g : Provenance ν κ) (T : TapeGraph) (m : Match ν)
    (r : Realized) : Bool :=
  (List.range T.size).all fun w =>
    !(T.parents w).any r.interior.contains || (m.body g r).contains w

/-- Progressing: every interior vertex feeds a sub-graph vertex, so it lies on a path to a
root. -/
def interiorProgress (g : Provenance ν κ) (T : TapeGraph) (m : Match ν)
    (r : Realized) : Bool :=
  r.interior.all fun p => (m.body g r).any fun w => (T.parents w).contains p

/-- Used: every frontier vertex feeds a sub-graph vertex — the realization reads every
component of every operand. -/
def frontierUsed (g : Provenance ν κ) (T : TapeGraph) (m : Match ν)
    (r : Realized) : Bool :=
  (m.frontier g r).all fun v => (m.body g r).any fun w => (T.parents w).contains v

/-- The sub-graph's vertices are operation vertices. -/
def bodyOps (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) (r : Realized) :
    Bool :=
  (m.body g r).all T.isOp

/-- A wire realizes only the identity wire or a procedure edge. -/
def wireOk (g : Provenance ν κ) (r : Realized) : Bool :=
  match familyOf g r with
  | some .copy => true
  | some (.step _ _ _) => true
  | _ => false

/-- One realization's clauses: a wire is a licensed wire; anything else is closed,
interior-private, progressing, used, and made of operation vertices. -/
def realizedOk (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) (r : Realized) :
    Bool :=
  if m.isWire g r then wireOk g r
  else
    realizedClosed g T m r && interiorPrivate g T m r && interiorProgress g T m r
      && frontierUsed g T m r && bodyOps g T m r

/-- Interiors are pairwise disjoint and disjoint from every component. -/
def interiorsDisjoint (m : Match ν) : Bool :=
  m.realized.all fun r => r.interior.all fun v =>
    !m.isComponent v && (m.realized.filter (·.interior.contains v)).length == 1

/-- Covering: every operation vertex lies in some non-wire realization. -/
def covering (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) : Bool :=
  T.ops.all fun v => m.realized.any fun r => !m.isWire g r && (m.body g r).contains v

/-- Every occurrence is realized. -/
def realizesAll (g : Provenance ν κ) (m : Match ν) : Bool :=
  (List.range g.occurrences.length).all fun i => m.realized.any (·.occ == i)

/-- Every realization names an occurrence. -/
def realizedInGraph (g : Provenance ν κ) (m : Match ν) : Bool :=
  m.realized.all fun r => r.occ < g.occurrences.length

/-- **Acceptance**: the match is what a matcher accepts and the bisimulation theorems
consume. Decided by evaluation in a probe and by kernel reduction in a theorem. -/
def accepts (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) : Bool :=
  T.ordered && totalOnNodes g T m && uniqueKeys m && keysDeclared g m
    && componentsDisjoint m && leavesAreSources g T m && sourcesAreLeaves g T m
    && m.realized.all (realizedOk g T m) && interiorsDisjoint m && covering g T m
    && realizesAll g m && realizedInGraph g m

/-- `Prop`-level acceptance, for statements and `decide`. -/
def Accepts (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) : Prop :=
  m.accepts g T = true

instance (g : Provenance ν κ) (T : TapeGraph) (m : Match ν) :
    Decidable (m.Accepts g T) :=
  inferInstanceAs (Decidable (m.accepts g T = true))

end Match

end PropertyKindCalculus.Paradigm

end Blanket
