# PKC CSE match-transport qualification

Status: **constructive identity-transport theorem established; topology residual isolated**

PKC baseline: `nasa-jpl/PropertyKindCalculus@6d3da52c1db4a085ac7ea561dd8f125e7cdb0fc9`

Prepared independently by: **Heath Sanchez / Metalogic Labs (MathGraph.org)**

Date: 2026-10-03

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
  certificate holds.

The same file proves `equal_constants_do_not_respect_distinct_sources`: the remap that
collapses the two source vertices in the original separator cannot satisfy
`CseRespectsMatch`. This makes the failure criterion executable as a theorem premise rather
than leaving it as prose.

The result has no `sorry`, `admit`, or `native_decide`. Both headline theorems have axiom
profile `[propext, Quot.sound]`.

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

## Exact residual to full `Match.Accepts` transport

This qualification deliberately does **not** claim the complete theorem

```text
m.Accepts g T
  ∧ CseRespectsMatch m q
  → (transportMatch q m).Accepts g T'
```

because ownership is necessary but not sufficient. A complete theorem must additionally
certify that the compacted graph `T'` is the graph quotient induced by `q`, including:

1. every mapped vertex is in range and every target vertex has a source preimage;
2. mapped parent lists agree with target parent lists;
3. leaf/operation status is preserved;
4. each realization remains closed, private, progressing, and frontier-using;
5. operation coverage survives; and
6. list multiplicity does not create duplicate realization ownership after mapping.

These are topology and multiplicity obligations, not metrological identity obligations.
Keeping them separate prevents a certificate named “respects match” from merely assuming
the desired final acceptance judgment.

The next non-tautological theorem should therefore introduce a `TapeQuotientCertificate`
for items 1–6 and prove:

```text
transport_accepts
  (old : m.Accepts g T)
  (identity : CseRespectsMatch m q)
  (topology : TapeQuotientCertificate T T' q m) :
  (transportMatch q m).Accepts g T'
```

PKC's existing `isWeakBisimulation_weak` and `isBisimulation_contracted` then apply without
being weakened or reproved.

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

The proof source is [`CseMatchTransport.lean`](./CseMatchTransport.lean). The prior concrete
CSE separator remains in
[`../mathgraph-cse-provenance-boundary-v1/`](../mathgraph-cse-provenance-boundary-v1/).

## Scope boundary

Established here:

- a concrete transported-match construction for an arbitrary vertex remap;
- a typed, non-numeric provenance identity contract;
- family-level preservation of component, interior, and role ownership;
- a proof that the existing equal-source-value separator violates that contract.

Not yet established:

- full Boolean `Match.Accepts` preservation;
- a `TapeQuotientCertificate` derived from every run of `cseCompact`;
- an admitted provenance quotient for intentionally shared scientific derivations;
- CUDA code-generation correctness below the tape;
- scientific validity against physical observations or truth of authored attestations.
