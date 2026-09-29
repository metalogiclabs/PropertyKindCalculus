import Verso
import VersoManual
import VersoBlueprint
-- Importing the library being documented lets the `(lean := "PropertyKindCalculus.…")`
-- nodes below resolve to real declarations and report their *proved* status. The graph
-- library carries the reachability reading of the pedigree closure that the first capstone
-- is argued over; the tape library carries the recording carrier and the denotation bridge
-- the second capstone rests on.
import PropertyKindCalculus
import PropertyKindCalculus.Graph.Flow
import PropertyKindCalculus.Torch.Paradigm.TapeParity

open Verso.Genre
open Verso.Genre.Manual
open Informal

#doc (Manual) "Capstone theorems — what the calculus can do" =>
%%%
tag := "capstones"
%%%

A reader who has followed the chapters so far knows what the calculus _is_: a kind is a
type index, two kinds meet only under a witnessed law, a boundary is declared and then
decided, and a model carries its attestations as hypotheses. The question a reviewer asks
first is a different one: _what can the calculus do?_ What guarantee does a model earn by
being written in it — stated as a theorem whose hypotheses the build discharges and whose
conclusion a reviewer can use without reading the model? Three theorems answer it, one per
layer of the calculus — the provenance layer, the computation layer and the dimension
layer, laid out below — read through {ref "paradigm"}[the taint-tracking paradigm]:

1. *The seal of a module.* Once a module's inputs, constants and attestations are
   declared, no other raw datum reaches its outputs: every leaf of an output's pedigree is
   a declared source. Stated over the {tech}[metrological provenance hypergraph] the
   build harvests from the module's members; its hypotheses are the two kernel-decided
   judgments the build already pins per boundary.
2. *The seal of the computation.* The same guarantee for the computation itself, at every
   carrier the module is instantiated at: an output depends only on the sources the
   hypergraph names for it, every constant it uses is one the audit lists, and every kind
   change in the computation sits at a declared crossing. Stated over the
   {tech}[computational tape graph] of the tape a carrier-generic module records, related to
   the provenance hypergraph by a {tech}[kind-transporting weak bisimulation].
3. *Dimensional homogeneity of the kind algebra.* Every derived kind in a well-formed
   provenance hypergraph carries the dimension the family rules compute from its operands,
   so the dimension functor is a homomorphism along every occurrence — not only along the
   edges an interaction algebra curates.

Four named objects appear in these statements, and this chapter keeps them apart. The
{tech}[metrological provenance hypergraph] is the kinded object the first capstone is
stated over, harvested from the source, and it is where every kind originates; the
{tech}[value-flow digraph] is its binary shadow, the graph reachability is proved on. The
{tech}[tape] is not a graph but a record — the sequence of carrier operations a module
writes when evaluated at the recording carrier — and the {tech}[computational tape graph]
is the directed acyclic graph that record determines, the object the second capstone
relates to the provenance hypergraph; it carries no kinds until the
{tech}[kind-transporting weak bisimulation] transports them. None of the four is the
{tech}[blueprint dependency graph] drawn at the end of this document, which is a picture of
the document itself.

This chapter is written blueprint-first, in the discipline {ref "proved-spine"}[the proved
spine] records after the fact: each theorem is stated informally with its hypotheses, its
proof is sketched against the declarations that exist, and the code-level refactoring each
sketch calls for is named as a work item in the ledger at the end. A node tagged _planned_
carries a statement and a sketch and no `lean` link; it turns _proved_ when the declaration
lands, and the status summary at the end of the blueprint counts both. Two rules govern
every statement below. *Non-vacuity is a deliverable, not a hope*: each capstone owes three
witnesses — an instance whose hypotheses the kernel decides, a mutant that fails the
hypothesis _and_ the conclusion, so that the hypothesis is shown to carry the weight, and a
pinned axiom profile. *The seal is no undeclared entry, not no entry*: raw data enters a
sealed module through its declared gates — a {tech}[checked ingest], a {tech}[constant
mint], an {tech}[attestation] with its reason — and the theorem's content is that the
build's list of gates is complete.

# The layers and their ladders

Each capstone is stated over one object, and those objects are the calculus's three
layers.

- *The provenance layer* — its object the {tech}[metrological provenance hypergraph]: what
  the source declares. Every node has a kind, every source has a tier, every hyperedge is
  a use of a law. Its value is that a module's assumptions become one object, and the seal
  of a module says that object's list of gates is complete for every output.
- *The computation layer* — its object the {tech}[computational tape graph]: what the code
  computes, at every carrier. Its value is that the seal becomes a claim about the
  executable rather than about a reading of the source.
- *The dimension layer* — its object the dimension functor over the kinds the hypergraph
  carries: what the laws in use must satisfy. Its value is that it is the only layer able
  to refute an authored law. Witnesses and attestations are claims; dimension can say no
  wherever the kinds carry one.

There is no single ladder from the first layer through the second to the third. There are
two ladders, and both stand on the provenance layer, because the computation layer checks
that the computation realizes the hypergraph while the dimension layer checks that the
laws inside the hypergraph cohere. A rung below both carries the source up to the
provenance layer. Each rung's status is the status of the nodes it names, which the
dependency graph and the ledger at the end of this chapter carry.

:::table +header
*
  * Rung
  * What carries it
  * Lost without it
*
  * Source to the provenance layer
  * the {tech}[boundary audit]; the {tech}[harvest]; {bpref "cap_def_wellFormed"}[well-formedness] and {bpref "def_contract"}[agreement of the declared boundary], decided per boundary; {bpref "cap_lem_pedigree_reachable"}[the reachability reading]; {bpref "cap_thm_seal"}[the seal of a module]
  * Per-site verdicts never compose to outputs: an anonymous mint two hops upstream of an output is visible only to a reader of the report.
*
  * Provenance layer to computation layer
  * {bpref "cap_lem_tape_cone"}[the cone lemma]; {bpref "cap_def_bisimulation"}[the bisimulation] with {bpref "cap_thm_bisimulation_sound"}[its soundness] and {bpref "cap_thm_strong_bisimulation"}[its strong form after contraction]; {bpref "cap_def_evaluates"}[the denotation bridge] and the closure tactic `tape_hom`; {bpref "cap_thm_semantic_seal"}[the seal of the computation]
  * The seal is about the harvest's transcript. A constant the recorder bakes, a path compaction introduces, an opaque callee the harvest saw as one node: all go unseen, and the harvest's attributions stay trusted instead of cross-checked.
*
  * Provenance layer to dimension layer
  * {bpref "thm_dim_homomorphism"}[the curated homomorphism]; the coverage command's verdict per authored edge; {bpref "cap_thm_dimensional_seal"}[dimensional homogeneity]
  * Outputs rest on declared sources through possibly wrong laws: a wrong edge is a kind-level fact nobody checks.
:::

The {tech}[kind-transporting weak bisimulation] is therefore the relation between the
provenance layer and the computation layer. It never touches the dimension layer directly,
but that layer's verdicts ride along it: every tape sub-graph that realizes an occurrence
realizes a law the dimension layer has judged coherent.

# The seal of a module — the provenance hypergraph

The first capstone is stated over the
{deftech}[metrological provenance hypergraph]{index}[metrological provenance hypergraph] —
the object every audit report presents one relation of. Its nodes are kinded values; its
hyperedges are occurrences of the witness families, each relating its operands to its
result _in order_, since a quotient's numerator and denominator are different ports of one
edge; its sources carry the {tech}[evidence tier] the boundary audit assigns them; and its
exits mark where a value leaves the calculus for the bare carrier. It is data — prelude-only,
parametric in the node and kind types — so it can be authored by hand in a probe or produced
by the {deftech}[harvest]{index}[harvest]: the elaboration-time walk that reads a declared
boundary's member definitions and builds their hypergraph from them, ports from the
members' signatures, occurrences from the kinded operations in their bodies, sources from
the tiers the {tech}[boundary audit] assigns and from the reason each attestation states at
its call site. The harvest's output for one boundary is its
{deftech}[assembly]{index}[assembly]: the hypergraph together with the signature positions
found to carry no kind and the level each node belongs to. The capstone's hypotheses are
the two judgments already decided per boundary: structural well-formedness of the
hypergraph, and agreement between the {tech}[declared boundary] and the one its members
compute. The order matters for what the seal rests on: the audit's tiers and the
attestations' reasons are inputs to the harvest, the harvest builds the hypergraph, and the
theorem is stated over that hypergraph with the two judgments as its hypotheses — the
audits establish the hypotheses, the harvest builds the object, and the theorem gives the
seal.

:::group "capstones_seal"
The seal of a module and what it rests on: well-formedness of the provenance hypergraph,
agreement of the declared boundary with the computed one
({uses "def_contract"}[the declared boundary]), and the reachability reading of the
pedigree. Everything the statement rests on exists and is proved; the theorem is the one
statement nobody has yet made over it.
:::

:::definition "cap_def_wellFormed" (parent := "capstones_seal") (lean := "PropertyKindCalculus.Provenance.wellFormed")
Structural well-formedness of the provenance hypergraph: every node declared exactly once;
every occurrence typed at its family's operand count, with operands and result carrying
their nodes' declared kinds; every occurrence result a derivation target — a `derived`
introduction or a produced port, never a source; and every derived node, produced port and
exit reached from the sources through the conjunctive closure of the occurrences. The last
clause is the boundary audit's "raw mints = 0" made compositional: a derived node no
occurrence chain produces is an anonymous mint, and an occurrence cycle feeding itself
licenses nothing, because the closure starts from the sources. `#kind_assembly_decide`
reflects the judgment into a kernel theorem per boundary.
:::

:::proof "cap_def_wellFormed"
Four structural recursions over lists, conjoined; decided by evaluation in a probe and by
kernel reduction in a theorem. The sources are the non-produced ports together with the
gated and attested introductions (`sources`), and the closure is a fuel-bounded fixpoint
that saturates in one sweep per occurrence (`reachableFrom`).
:::

:::definition "cap_def_pedigree" (parent := "capstones_seal") (lean := "PropertyKindCalculus.Provenance.ancestorsOf")
The {deftech}[pedigree]{index}[pedigree] of a node set: everything it is derived from, the
set itself included — the backward closure through the occurrences, computed as the forward
influence closure of the reversed incidence, one reversed unit occurrence per operand
position. The sources among an output's pedigree are its
{deftech}[influencers]{index}[influencers]: the term list of an uncertainty budget over the
hypergraph's edges, and the source set whose attached conditions a downstream flag may
claim for that output. Split by what each source _is_, the same set is the output's
{deftech}[assumption ledger]{index}[assumption ledger]: the ports left open at the
boundary, the gated ingests, the attested mints with their harvested reasons.
:::

:::proof "cap_def_pedigree"
One engine for both directions: the disjunctive sweep that adds a result when _some_
operand is known, run over the occurrence list reversed edge by edge. Fuel is one sweep per
reversed occurrence plus one, the sweep that observes saturation.
:::

:::theorem "cap_lem_pedigree_reachable" (parent := "capstones_seal") (lean := "PropertyKindCalculus.Provenance.mem_ancestorsOf_iff") (tags := "proved") (effort := "small")
Membership in the executable pedigree is reachability in the
{deftech}[value-flow digraph]{index}[value-flow digraph] — the binary shadow of the
provenance hypergraph, one vertex per node and one edge per operand-to-result pair of an
occurrence: `a` is among the ancestors of `b` exactly when a path of such edges leads from
`a` to `b`. This is the lemma that lets the capstone below be argued over paths while its
hypotheses are decided over lists.
:::

:::proof "cap_lem_pedigree_reachable"
The saturation argument for the forward closure — a sweep only appends, appended nodes are
pairwise-distinct occurrence results, so with one sweep per occurrence plus one the closure
has either observed a fixpoint or would have outgrown its own bound — applied to the
reversed incidence, whose step relation is the converse of the flow digraph's adjacency.
:::

:::theorem "cap_thm_seal" (parent := "capstones_seal") (tags := "capstone, planned") (effort := "medium") (priority := "high")
*The {deftech}[seal of a module]{index}[seal of a module].* Let `g` be a provenance
hypergraph and `c` a declared boundary, with `g` {uses "cap_def_wellFormed"}[well-formed]
and `c` agreeing with `g` — the two judgments `#kind_assembly_decide` and
`#kind_contract_decide` pin ({uses "def_contract"}[the declared boundary]). Then for every
produced port or exit `y` of `c`, every node `a` in {uses "cap_def_pedigree"}[the pedigree
of `y`] is either a source of `g` — a non-produced port of `c`, a gated ingest, or an
attested mint carrying its reason — or the result of some occurrence all of whose operands
are themselves in the pedigree of `y`. Equivalently: the pedigree of an output has no leaf
outside the sources, and the assumption ledger the build prints for `y` is the complete
list of what `y` rests on. In the paradigm's words, once the module's gates are declared,
no other raw datum reaches its outputs.
:::

:::proof "cap_thm_seal"
By {uses "cap_lem_pedigree_reachable"}[the reachability reading], a node `a` in the
pedigree of `y` lies on a path to `y`, so `a` is an operand of some occurrence, and
`occurrencesTyped` makes it a declared node — a port or an introduction. If `a` is a
non-produced port or a gated or attested introduction, it is a source. Otherwise `a` is a
`derived` introduction or a produced port, and `sourcesReach` places it in the conjunctive
closure `known`, so some occurrence produces `a` with every operand in `known`; each such
operand is an ancestor of `a`, hence of `y` by transitivity of reachability. The hypothesis
on `c` enters only to identify the non-produced ports of `g` with the boundary's declared
inputs, configuration and parameters, so that the conclusion speaks of the declared
interface rather than of whatever the harvest happened to port. The executable form — a
decidable `undeclaredLeaves g y`, empty exactly under the conclusion — is the same induction
stated as a `Bool`, and it is what an instance pins with `decide`. The theorem belongs
beside the reachability reading, in the graph library.
:::

:::theorem "cap_thm_seal_witnesses" (parent := "capstones_seal") (tags := "planned") (effort := "small")
*Non-vacuity of the seal.* Three witnesses, each a pinned probe. (i) An instance: a declared
boundary of the worked model whose well-formedness and agreement the kernel already decides,
for which `decide` closes the executable conclusion at every produced port. (ii) A mutant:
the same hypergraph with one anonymous mint added — a `derived` introduction no occurrence
produces, wired into an output — fails `wellFormed` _and_ has a non-empty
`undeclaredLeaves` at that output, so the hypothesis is the discriminating one and the
conclusion is not closed by the shape of the statement. (iii) The axiom profile of
{uses "cap_thm_seal"}[the seal], pinned to the three classical axioms.
:::

:::proof "cap_thm_seal_witnesses"
(i) and (ii) are `#guard` and `decide` probes over harvested and authored hypergraphs;
(iii) is `#print axioms` under `#guard_msgs`. The mutant is the check the methodology asks
of every gate — a tactic that closes a goal is not evidence that the hypothesis fired —
carried into the capstone itself.
:::

What the first capstone does not claim: it is a theorem about the provenance hypergraph the
harvest produced. That the hypergraph is the code — that the harvest attributed every mint,
erasure and occurrence to the right node and missed none — is what the boundary audit, the
mint ratchet and the unkinded sweep assert about the source, and each of those is an
instrument, not a hypothesis of the theorem. The seal of the computation is what turns that
residual trust into a cross-check.

# The seal of the computation — the tape

A carrier-generic module has a second record of its computation, one that no harvest
produces. The {deftech}[tape]{index}[tape] is automatic differentiation's word for the
record of the operations a program performs, in the order it performs them. TorchLean's
autograd tape is that record as data: a grow-only array of nodes, each one operation with
the ids of its parents in operand order, its forward value and its local backward rule, and
every operation appends exactly one node. The name comes from reverse-mode differentiation,
which replays the record backward to accumulate gradients; the calculus never runs that
pass. It reads the tape forward — the code generator lowers it, and the evaluator the cone
lemma below is about re-computes every node from an environment of leaf values. A tape is
therefore a straight-line program, not a graph. A module writes one when instantiated at
the {deftech}[recording carrier]{index}[recording carrier] — the carrier whose values are
not numbers but thunks that append their sub-expression to the tape and return the result
node. Because the branchless carrier class carries no ordering to `Bool`, a module written
against it cannot branch on its data, so one recording covers every input.

The {deftech}[computational tape graph]{index}[computational tape graph] is the directed
acyclic graph the record determines: one vertex per tape node, an edge from each parent to
its node, the in-edges of a vertex ordered as its parents are — acyclic because every
parent precedes its node in the array. Its leaves are of exactly two sorts, a named input
and a baked constant; its roots are the recorded outputs; and it carries no kinds, since a
value of any kind records the same node. The name pairs it with the metrological
provenance hypergraph: one is what the source declares about kinds, the other is what the
code computes, and the second capstone is the relation between them. Graph or hypergraph?
A tape node _is_ its operation, so a vertex's ordered in-edges are the one hyperedge into
it, and reading the tape as an ordered hypergraph adds nothing to the graph. The provenance
hypergraph is a hypergraph in a stronger sense: its occurrences are objects apart from its
nodes, and several occurrences may derive one node. The
{deftech}[compacted tape]{index}[compacted tape] — the tape after its identical
sub-expressions are merged, so that its graph is the graph of the _distinct_ sub-expressions
rather than of their unfolding — is the very object the code generator lowers to a kernel.

:::group "capstones_semantic"
The seal of the computation: the second capstone relates the tape graph to the provenance
hypergraph, transports the hypergraph's kinds onto it through a weak bisimulation, and
states the seal for the computation at every carrier through the denotation bridge.
:::

:::definition "cap_def_tape" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Paradigm.TapeBuilder")
The recording carrier, as a structure: one deferred build action that, run inside the tape
monad, appends this sub-expression's nodes and yields its result node. Every
branchless-carrier operation is realized as one appended node, so instantiating a module at
this carrier _builds_ its tape, with one leaf per named input and one per host constant.
:::

:::proof "cap_def_tape"
Each arithmetic operation runs its operands and emits one node. Sharing is not recorded — a
sub-expression named twice emits twice — and the compaction that merges identical
sub-expressions is a separate pass over the recorded tape.
:::

:::definition "cap_def_evaluates" (parent := "capstones_semantic") (lean := "PropertyKindCalculus.Paradigm.TapeParity.Evaluates")
The {deftech}[denotation bridge]{index}[denotation bridge]: a recording-carrier value
_evaluates_ to a tensor when, on any tape, running it succeeds, its result node carries that
tensor, and the run only extends the tape. Each carrier operation preserves the bridge with
its matching elementwise operation, proved once per operation, so a module's parity with its
own eager value at the same source is the mechanical chaining of those lemmas — and needs
no numerical side condition, both carriers using the same clamped operations.
:::

:::proof "cap_def_evaluates"
A four-conjunct predicate; the per-operation preservation lemmas are proved from the tape's
forward-value faithfulness lemmas through a run bridge, and a composite kernel's parity is a
chain of them.
:::

:::theorem "cap_lem_tape_cone" (parent := "capstones_semantic") (tags := "planned") (effort := "small")
*Evaluation reads only the cone.* Re-evaluating a tape from an environment of leaf values
gives, at every node, a value that depends only on the leaves in that node's backward cone
in the tape graph: two environments agreeing on the cone's named leaves give the same value
at the node. The
tape-side counterpart of {uses "cap_lem_pedigree_reachable"}[the pedigree reading].
:::

:::proof "cap_lem_tape_cone"
Structural induction over the topologically ordered node list the evaluator walks: a leaf
reads its own name or constant, and an operation applies its scalar to values already
established for its parents, each of which lies in the cone.
:::

:::definition "cap_def_bisimulation" (parent := "capstones_semantic")
*The {deftech}[kind-transporting weak bisimulation]{index}[kind-transporting weak bisimulation].*
The relation that ties the two graphs of one module together: the provenance hypergraph
`g`, harvested from the source, where every kind originates, and the computational tape
graph of the tape `T` the same module records, which carries none. `R` relates nodes of `g`
to vertices of the tape graph. It is total on the _observable_ vertices — leaves, roots, and the operands and
results of every matched occurrence — and silent on the interior vertices a single kinded
operation expands to at the carrier: the real projections of a complex product, the
sub-graph of a principal square root, the plumbing an operation registered as carrier
vocabulary performs. That silence is what makes it _weak_: an interior vertex is a step
neither side observes. It simulates in both directions, which is what makes it a
_bisimulation_. Hypergraph to tape: every occurrence of `g` is matched to a tape sub-graph
whose frontier is the images of the occurrence's operands and whose operations realize the
occurrence's family, per a realization table with one entry per family and carrier. Tape to
hypergraph: every path of the tape graph between observable vertices projects along `R` to
a path of `g` — the direction the seal consumes. `R` matches leaves to sources, ports by
name and constants by value. A `step` edge to a member whose audit tier licenses a
re-typing is realized by a wire, and it is the only place the kinds transported along `R`
may change across a tape edge. The coarsest reading `R` preserves is the boundary's
{deftech}[propagation relation]{index}[propagation relation] — which source ports reach
which produced ports through the occurrences — and comparing that relation, rather than
occurrence lists, is what makes the match robust to sharing. `R` is not a bijection, for
four reasons present in the code: compaction merges tape nodes many-to-one; one kinded
operation is several carrier operations; two uses of one witness are two occurrences by
design; and a nominal selection is resolved at recording time into one tape per branch.
:::

:::proof "cap_def_bisimulation"
Computed, never assumed: a bottom-up matcher from the leaves, deciding per occurrence
whether the realization table admits the tape sub-graph it finds, and refusing otherwise.
The definition names the refactoring this capstone prices: the recorder must name its
constant leaves, and either mark the scope of each member call on the tape or the matcher
must widen the member set to the closure the tape sees through.
:::

:::theorem "cap_thm_bisimulation_sound" (parent := "capstones_semantic") (tags := "planned") (effort := "medium")
*The matcher is sound.* When the matcher accepts `R` for `g` and `T`, the tape-to-hypergraph
direction of {uses "cap_def_bisimulation"}[the bisimulation] holds: every path of the tape
graph from a named leaf to a root projects along `R` to a path of `g` from the
corresponding source to the corresponding produced port, and the kinds transported along
`R` change only across the image of a licensed `step`. The other direction — every
occurrence of `g` realized on the tape — is what acceptance checks occurrence by occurrence,
so it holds by construction of the matcher; the direction stated here is the one the seal
consumes and the one that needs a proof. The tape-side analogue of the lemma that makes the
influence probe's `false` a theorem — so an accepted match is evidence rather than a report.
:::

:::proof "cap_thm_bisimulation_sound"
Induction over the matcher's acceptance derivation, one case per family of the realization
table; each case is a small path lemma about the sub-graph the entry admits.
:::

:::definition "cap_def_contraction" (parent := "capstones_semantic")
*The {deftech}[contracted tape graph]{index}[contracted tape graph].* Let the matcher have
accepted `R` for `g` and `T`, so that each occurrence `o` of `g` has a realizing sub-graph
`S_o` of the tape graph. The contraction collapses each `S_o` to one ordered hyperedge:
its operands are the frontier of `S_o` in the occurrence's operand order, its result is the
root of `S_o`, and its label is the occurrence's family. It is defined — it yields an
acyclic ordered hypergraph of the same signature as `g` — under four conditions on the
sub-graphs, which the acceptance derivation records: _convex_, every tape path between two
vertices of `S_o` stays inside `S_o`, so no contraction creates a cycle;
_interior-private_, every edge leaving an interior vertex of `S_o` stays inside `S_o`, so
no interior value is read from outside; _disjoint_, the interiors of distinct sub-graphs do
not overlap; and _covering_, every operation vertex of the tape graph lies in some `S_o`.
Leaves are matched by recording site, not by value, so that two constants of one value
stay two leaves.
:::

:::proof "cap_def_contraction"
A quotient of the tape's vertex set by the interiors, with one hyperedge per accepted
occurrence; the four conditions are decided over the acceptance derivation, and a
sub-graph violating one is a match the matcher refuses. The recorder's obligation is the
named constant leaf, the same one the bisimulation's definition already prices.
:::

:::theorem "cap_thm_strong_bisimulation" (parent := "capstones_semantic") (tags := "planned") (effort := "medium")
*Contraction makes the bisimulation strong.* Under the four conditions of
{uses "cap_def_contraction"}[the contraction], `R` restricted to the observable vertices is
a strong bisimulation between `g` and the contracted tape graph — every step on one side
is matched by exactly one step on the other, with no silent step — and, once the two
node-identity mismatches are quotiented away, an isomorphism of ordered hypergraphs:
compaction, by comparing against the uncompacted tape or by quotienting `g` by derivation
equality; nominal selection, by comparing per branch. {uses "cap_def_bisimulation"}[The
weak bisimulation] between `g` and the tape graph then factors as this strong one composed
with the contraction, which is the standard relation between weak and strong bisimulation
up to silent-step abstraction. What the strong form deliberately loses is the interior,
and the interior is where the numerical side conditions live: the license clause and the
adequacy layer keep working on the uncontracted tape graph.
:::

:::proof "cap_thm_strong_bisimulation"
One contraction lemma: convexity and interior privacy give that every path of the
contracted graph between observable vertices lifts to a path of the tape graph through
interiors and projects, by {uses "cap_thm_bisimulation_sound"}[soundness of the matcher],
to a path of `g`; coverage and disjointness give the converse, one hyperedge per
occurrence. No new instrument: the acceptance derivation already decides the four
conditions, so the strong form is a corollary of acceptance.
:::

:::theorem "cap_thm_semantic_seal" (parent := "capstones_semantic") (tags := "capstone, planned") (effort := "large") (priority := "high")
*The {deftech}[seal of the computation]{index}[seal of the computation].* Let `f` be a
module written once against the branchless carrier class with fixed-extent iteration, `g`
its provenance hypergraph with `c` its declared boundary, and `T` the tape `f` records.
Suppose (H1) {uses "cap_thm_seal"}[the seal of the module] holds of `g` and `c`; (H2) the
matcher accepts a bisimulation `R` between `g` and the computational tape graph of `T`;
and (H3) at every carrier, `f`
{uses "cap_def_evaluates"}[evaluates] to the re-evaluation of `T` from its inputs. Then at
every carrier and for every produced port `o`: two inputs that agree on the influencers of
`o` — the sources `g` names for it — give the same value of `o`; every constant the
computation uses is one the audit lists; and every kind change in the computation sits under
a declared crossing. The hypergraph's absence claims become semantic: an input the harvest
says cannot reach `o` provably does not, in the computation, at every carrier.
:::

:::proof "cap_thm_semantic_seal"
By (H3) the value of `o` at any carrier is the tape's value at the root `R` assigns to `o`;
by {uses "cap_lem_tape_cone"}[the cone lemma] that value depends only on the leaves in the
root's cone; by {uses "cap_thm_bisimulation_sound"}[soundness of the matcher] those leaves
are the images of the sources in the pedigree of `o`, which (H1) identifies with the
declared influencers and the listed constants. The kind clause is the soundness theorem's
second half, read back through `R`.
:::

:::theorem "cap_thm_semantic_seal_witnesses" (parent := "capstones_semantic") (tags := "planned") (effort := "medium")
*Non-vacuity of the seal of the computation.* (i) An instance where all three hypotheses
are discharged by theorem: the worked model's branchless dielectric chain and its
reflectivity, whose hypergraph is pinned, whose tape is recorded, and whose (H3) is already
a chain of `Evaluates` lemmas. (ii) A mutant: a recording that bakes one constant the audit
does not list — the matcher refuses `R`, and the conclusion's constant clause fails.
(iii) The axiom profile of {uses "cap_thm_semantic_seal"}[the seal of the computation],
pinned.
:::

:::proof "cap_thm_semantic_seal_witnesses"
(i) is the matcher run on a pair of objects that already exist; (ii) is a probe; (iii) is
`#print axioms`. Where (H3) is only a bit-exact runtime gate — the iterated retrieval, the
table lookups — the instance is gated, not proved, and the ledger says so.
:::

What the second capstone changes, and what it leaves. It covers bits and, through `R`,
kinds: the tape graph's kinds are the hypergraph's, transported, and the matcher checks the
hypergraph's occurrence structure — each family against the operation that realizes it —
against an instrument the harvest does not share. Read as a guarantee about the code: every
occurrence maps to a tape sub-graph realizing its family, every tape path between
observable vertices projects to a hypergraph path, and the kinds transported along `R`
change only at the image of a declared crossing — so the computation is kind-preserving in
exactly that sense, on a graph that carries no kinds of its own; and speaking of values at
every carrier needs (H3), the denotation bridge, beside it. What remains trusted is
smaller: that the harvest read each node's kind off the kernel-checked term at the right
node, since `R` transports kinds and does not re-derive them; and the code generator and
toolchain below the tape, which {ref "deployment-template"}[the deployment template] lists
as such.

# Dimensional homogeneity along the hypergraph

Three results grow in scope here, and the third capstone is the jump from the first two to
the third. {bpref "thm_dim_homomorphism"}[The curated homomorphism] is proved: for a
curated interaction algebra, whenever the algebra sanctions a product, the result's
dimension is the product of the operands' dimensions. It holds because the algebra carries
that side condition in its definition, so it is per algebra, and only for the product and
quotient edges an author chose to mirror into one. The coverage command is mechanical: it
walks every authored edge under a namespace across all nine witness families and evaluates
each family's dimensional rule. It is total, but per edge, and its output is a report
rather than a theorem. The capstone below composes both: given a well-formed hypergraph
whose occurrences all carry coherent families, dimension is a homomorphism along every
occurrence and hence along every path, so the dimension of every derived node and every
output is the one computed from the sources' dimensions by composing the rules. A per-edge
verdict says each step balances; the capstone says the whole model balances end to end —
dimensional analysis of the entire algorithm as a theorem — and it covers the families the
model actually uses, transcendental, power, copy and difference among them, which no
interaction algebra curates. In the paradigm's words: the seal of a module says nothing
undeclared enters, and homogeneity says every law traversed coheres, so an output's kind
rests on declared sources through coherent laws.

:::group "capstones_dimension"
The kind algebra's edges are authored claims: a product witness proves only that its three
kinds are ratio-scale, and that _these_ kinds meet is the author's metrological claim. One
layer can refute such a claim — the dimension functor, where a wrong edge over dimensioned
kinds fails to balance — and the coverage command walks every authored edge and reports it
coherent, parametric, or refuted. The third capstone lifts the per-edge verdict to the
hypergraph: dimension is a homomorphism along every occurrence of a well-formed provenance
hypergraph, not only along the edges an interaction algebra curates.
:::

:::theorem "cap_thm_dimensional_seal" (parent := "capstones_dimension") (tags := "capstone, planned") (effort := "medium") (priority := "high")
*{deftech}[Dimensional homogeneity]{index}[dimensional homogeneity] along the hypergraph.*
Let `g` be a {uses "cap_def_wellFormed"}[well-formed] provenance hypergraph each of whose
occurrences carries a family whose dimensional rule holds of its kinds' declared
dimensions — a product adds the operand exponents, a quotient subtracts them, a reciprocal
negates them, a power scales them by its exponent, a transcendental demands dimension one,
a copy preserves — the verdict the coverage command reports as `[coherent]` for every
non-parametric edge in scope. Then the dimension of every derived node equals the dimension
the rules compute from its operands' dimensions, and hence from the sources' alone: the
dimension functor is a homomorphism along every path of `g`. The hypergraph-level, total
form of {uses "thm_dim_homomorphism"}[the curated homomorphism], which is per edge and per
algebra.
:::

:::proof "cap_thm_dimensional_seal"
Induction over the conjunctive closure from the sources, one case per family, each closed by
the family's rule; well-formedness supplies that every derived node is produced by some
occurrence with known operands. The refactoring this capstone prices is that the coverage
rows must become data the hypergraph can carry — a dimension per kind reference, a verdict
per occurrence — the way the boundary audit's tiers became `IntroTier` on the hypergraph;
the command's report is today a rendered string. Non-vacuity: the pinned refutation of an
`L · L → L` edge, and a mutant occurrence of that shape that fails the hypothesis and the
conclusion together.
:::

# Status ledger

*Done — what each capstone rests on, all of it proved or decided today.*

- The provenance hypergraph with its well-formedness judgment, the pedigree closure and its
  reachability reading, the boundary judgments `agrees` and `discharges`, and the
  per-boundary kernel theorems the worked model pins for each of its declared boundaries.
- The recording carrier, the compaction pass, the code generator, and the denotation bridge
  with whole-kernel parity theorems for the branchless dielectric chain, its reflectivity,
  and the fit's forward, residual and Jacobian kernels.
- The dimension functor, the curated homomorphism, and the coverage command with its pinned
  refutation of an incoherent edge.

*Open — each item with whose move it is.*

- Capstone 1: state and prove the seal of a module (`cap_thm_seal`) beside the
  reachability reading, with its executable form and its three witnesses. Nothing to
  design; a proof-writing session. *Library.*
- Capstone 2, instrument before theorem: run the matcher on the dielectric pair, where the
  hypergraph, the tape and the parity theorem all exist, and read what disagrees before
  pricing the seal of the computation (`cap_thm_semantic_seal`); the expected disagreement
  classes are the four named in the bisimulation's definition (`cap_def_bisimulation`).
  *Library and worked model.*
- Capstone 2, the recorder decision: scope markers per member call, or membership widened
  to the closure the tape sees through — the choice that fixes the matcher's cost. *Owner.*
- Capstone 2, the contraction lemma (`cap_thm_strong_bisimulation`): a corollary of
  acceptance once the matcher exists, with no instrument of its own. *Library.*
- Capstone 2, the iterated retrieval's parity theorem, today a bit-exact runtime gate.
  *Worked model.*
- Capstone 3: the coverage rows as hypergraph data, then the induction. *Library.*

# What the capstones do not claim

- The truth of an attestation. It is a hypothesis of the model; the seal says only that the
  build's list of them is complete.
- The harvest's kind readings. The bisimulation transports them and does not re-derive them.
- Anything below the tape — the code generator, the toolchain, the foreign interface — which
  the deployment template lists as what remains trusted.
- Accuracy against nature, which needs a true value the kernel never has; that boundary is
  the uncertainty chapter's.
