# PKC CSE match-transport qualification

Status: **executable quotient admission and the actual recorded worked-model CSE path qualified**

PKC baseline: `nasa-jpl/PropertyKindCalculus@6d3da52c1db4a085ac7ea561dd8f125e7cdb0fc9`

Prepared independently by: **Heath Sanchez / Metalogic Labs (MathGraph.org)**

Date: 2026-10-03--04

Manager-facing synthesis: [`INDEPENDENT_REVIEW.md`](./INDEPENDENT_REVIEW.md)

## Executive result

The first MathGraph qualification established that the present executable CSE pass cannot
unconditionally preserve PKC provenance: two equal anonymous constants can be merged even
when they represent different attested sources. This follow-on turns that separator into a
positive contract.

`CseMatchTransport.lean` now defines:

- `transportMatch q m`, the match obtained by mapping every component and realization
  interior through a compaction remap `q`;
- `CseRespectsMatch m q`, with three independent provenance-sensitive obligations:
  component ownership, realization-interior ownership, and separation of observable
  components from silent interiors; and
- `transport_preserves_protected_partition`, a family-level Lean theorem proving that the
  transported match preserves all three protected ownership relations whenever the
  identity certificate holds;
- `TapeQuotientCertificate`, the explicit optimization-admission evidence object for the
  target tape graph; and
- `transport_accepts`, which composes source acceptance with that certificate to prove
  full target `Match.Accepts`.

Two immediate corollaries close the abstract optimization consequence:

- `transport_strong_bisimulation` reuses PKC's existing contraction theorem to establish
  a strong bisimulation between the authored provenance graph and the contracted optimized
  tape; and
- `transport_weak_bisimulation` reuses PKC's existing theorem to establish the
  kind-transporting weak bisimulation against the uncontracted optimized tape.

The same file proves `equal_constants_do_not_respect_distinct_sources`: the remap that
collapses the two source vertices in the original separator cannot satisfy
`CseRespectsMatch`. This makes the failure criterion executable as a theorem premise rather
than leaving it as prose.

The result has no `sorry`, `admit`, or `native_decide`. `transport_accepts`, the strong
bisimulation corollary, the lawful-sharing acceptance witness, and the two identity theorems
have axiom profile `[propext, Quot.sound]`. The weak-bisimulation corollary inherits
`Classical.choice` from PKC's existing weak-bisimulation theorem.

The follow-on modules close two further gaps:

- `CseQuotientChecker.lean` makes every certificate field executable and proves the Boolean
  audit sound and complete for `TapeQuotientCertificate`; and
- `RecordedCseQualification.lean` runs PKC's actual recorder and `cseCompact` on the complex
  worked model, pins the 18-to-14 vertex remap, and proves that the resulting audit yields
  target acceptance plus both bisimulation capstones; and
- `CertifiedCseGate.lean` and `CertifiedCseControls.lean` make that chain a proof-carrying
  admission operation with complete named rejection residuals and executable adversarial controls.

## What has changed conceptually

The optimization boundary can now be stated precisely:

```text
structural/numeric equality
          │
          ▼
candidate CSE remap q
          │
          ├── preserves provenance ownership ──► transport protected match identity
          │
          └── erases protected ownership ──────► reject or quotient provenance explicitly
```

The contract does not require CSE to be globally injective. It permits exactly the sharing
that does not collapse a distinction protected by the current match. That is the useful
middle ground between disabling CSE and trusting equal raw values as semantic identity.

## The certificate boundary

This qualification now proves the complete compositional theorem

```text
m.Accepts g T
  ∧ TapeQuotientCertificate g T' m q
  → (transportMatch q m).Accepts g T'
```

The certificate includes `CseRespectsMatch` as the scientific-identity boundary and exposes
the exact remaining target-side `Match.accepts` residuals separately:

1. target ordering and totality;
2. component disjointness after mapping;
3. leaf/source correspondence in both directions;
4. realization closure, privacy, progress, frontier use, and operation-only interiors;
5. realization-interior disjointness; and
6. operation coverage.

The certificate does **not** contain an `Accepts` field. The source-stable key, declaration,
occurrence-completeness, and occurrence-range clauses are transported by separate lemmas;
the theorem reconstructs the target acceptance conjunction. This prevents the evidence
object from merely renaming the desired conclusion.

The lawful-sharing graph control proves that the collapse is admissible when both vertices
belong to one attested source. Together with the preceding executable CSE qualification,
which observes the same `0 ↦ 0, 1 ↦ 0` remap for two equal anonymous constants, this gives
linked positive and negative controls for the boundary without claiming that kernel reduction
executed Torch's external tensor primitives.

`CseQuotientChecker.lean` turns all of these obligations into a finite Boolean audit. Its
`TapeQuotientAudit.sound` theorem constructs the certificate from a passing audit, while
`TapeQuotientAudit.complete` proves that the audit accepts every certificate. The audit can
therefore be placed directly at the optimization/code-generation boundary.

The remaining family-level generalization is narrower: prove conditions under which arbitrary
`cseCompact` runs are guaranteed to pass the audit. The practical alternative is now implemented
by `certifyCse`: it executes the actual transform and refuses admission unless the complete finite
audit passes. This does not replace a universal proof of the imperative loop; it makes every
concrete decision explicit and independently replayable.

## One-command certification demonstrator

```bash
experiments/mathgraph-cse-match-transport-v1/pkc-certify all
```

The worked recording returns `CERTIFIED` with the exact 18-to-14 remap and theorem authority for
accepted matching plus strong and weak bisimulation. Equal constants belonging to distinct
attested sources return `REJECTED` with `component-ownership` and `component-multiplicity`. Adding
one undeclared constant to the worked recording returns `REJECTED` with
`source-match-acceptance` and `leaves-are-sources`.
Every audit bit is printed, and the command appends a SHA-256 digest of its manifest.

## Actual recorded worked-model qualification

The qualification records PKC's existing complex model `y = a * b + e` through the real tape
recorder. Before CSE the tape has 18 vertices. Running the actual `cseCompact` implementation
produces the existing 14-vertex PKC control tape with remap:

```text
[0, 1, 2, 3, 4, 5, 6, 7, 8, 0, 4, 9, 3, 1, 10, 11, 12, 13]
```

The source match is accepted on the raw graph. Its transported form, after erasing only duplicate
vertex identifiers introduced by sharing repeated emissions, equals PKC's independently authored
compacted match. The complete quotient audit passes. Ordinary Lean theorems then establish:

- `recorded_cse_accepts`;
- `recorded_cse_strong_bisimulation`; and
- `recorded_cse_weak_bisimulation`.

The executable observation and mathematical proof are deliberately separated. `#guard` pins the
concrete recorder, CSE result, graph projection, remap, and control-match correspondence. Kernel
proofs establish audit soundness, acceptance transport, and bisimulation on those reified objects.
This qualifies the concrete run; it is not a universal theorem about the imperative CSE loop.
The audit qualifies provenance correspondence, not numerical equivalence of source and target
tapes; a generic denotation-preservation theorem for `cseCompact` remains separate.

## Value to the PKC methodology

For Nicolas, this supplies the missing optimization-admission boundary in theorem form:
an executable transform is not accepted because it preserves Float results alone; it must
carry a certificate that the distinctions used by the metrology/provenance match survive.

For Xiaolan's science case, the eventual evidence object can name every merge, the protected
scientific identities it was checked against, and the topology certificate used to carry the
accepted match onto the CPU/GPU graph. A NASA manager can then distinguish three claims:

- the science algorithm is sealed and kinded;
- the optimization was admitted under an explicit machine-checked contract; and
- the deployed graph remains connected to the authored provenance graph by PKC's existing
  bisimulation theorems.

That is stronger and more auditable than a benchmark plus a numerical regression test.

## Evidence and reproduction

Run from the repository root:

```bash
experiments/mathgraph-cse-match-transport-v1/verify.sh
```

The proof sources are [`CseMatchTransport.lean`](./CseMatchTransport.lean),
[`CseQuotientChecker.lean`](./CseQuotientChecker.lean), and
[`RecordedCseQualification.lean`](./RecordedCseQualification.lean),
[`CertifiedCseGate.lean`](./CertifiedCseGate.lean), and
[`CertifiedCseControls.lean`](./CertifiedCseControls.lean). The prior concrete CSE separator remains in
[`../mathgraph-cse-provenance-boundary-v1/`](../mathgraph-cse-provenance-boundary-v1/).

## Scope boundary

Established here:

- a concrete transported-match construction for an arbitrary vertex remap;
- a typed, non-numeric provenance identity contract;
- family-level preservation of component, interior, and role ownership;
- a proof that the existing equal-source-value separator violates that contract;
- a non-tautological `TapeQuotientCertificate`;
- full `Match.Accepts` transport;
- strong bisimulation against the contracted optimized tape;
- weak bisimulation against the uncontracted optimized tape; and
- a lawful-sharing witness for two emissions of one attested source;
- a sound-and-complete executable audit for the quotient certificate;
- a pinned execution of the actual recorder and `cseCompact` on PKC's worked model; and
- accepted-match plus strong/weak-bisimulation consequences for that optimized concrete model.
- a proof-carrying `certifyCse` result that unlocks those consequences on success;
- a complete stable rejection vocabulary over source acceptance and all eleven quotient clauses;
  and
- a one-command worked-model and adversarial certification manifest.

Not yet established:

- a `TapeQuotientCertificate` derived universally from every run of `cseCompact`;
- numerical denotation preservation for every `cseCompact` run;
- automatic inference of a `Match` for an arbitrary recorded computation;
- graph isomorphism (strong bisimulation is established; isomorphism is a stronger and
  separate claim);
- an admitted provenance quotient for intentionally shared scientific derivations;
- CUDA code-generation correctness below the tape;
- scheduler and checkpoint/resume refinement below the tape; and
- scientific validity against physical observations or truth of authored attestations.
