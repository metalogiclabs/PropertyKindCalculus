# PKC Recording Matcher Design

## Purpose

Close PKC's operational matching gap without claiming information that the recorded tape does not
contain. The result must either produce a checked correspondence and downstream CSE/bisimulation
authority, expose genuine ambiguity, or return a named local obstruction. Work remains on the
Metalogic Labs fork; no upstream NASA/JPL notification or pull request is created.

## Authority boundary

The matcher consumes a provenance graph, recorded tape graph, and explicit evidence plan. The
plan supplies the information erased by `TapeGraph`: port names, constant recording-site identity,
and occurrence family/carrier realization shapes. Dependency closure infers realization interiors.

Every generated candidate is passed through PKC's existing `Match.accepts`. No candidate can be
returned as inferred without retaining its acceptance proof.

## Protected consequence equivalence

Literal `Match` table equality is not semantic identity. For a fixed provenance graph and tape,
the matcher canonicalizes each accepted candidate to a protected consequence signature containing:

1. the provenance owner of every observable tape component;
2. each occurrence's canonical frontier, observable roots, and silent interior; and
3. the occurrence owner of each operation vertex.

Lists are canonicalized in tape order, so table order and duplicate entries cannot create false
ambiguity. Accepted candidates with the same signature form one consequence class.

## Typed outcomes

- `INFERRED`: exactly one protected consequence class. It contains one or more accepted candidate
  matches, the shared correspondence signature, and the representative used downstream.
- `AMBIGUOUS`: at least two consequence classes. It contains representatives and the smallest
  first differing component/occurrence/operation witness.
- `REJECTED`: no candidate is accepted. It contains the complete stable acceptance-clause
  residuals and a smallest locally detectable conflicting tape/provenance region.

The worked-model result is promoted only to `WARRANTED_BOUNDED`.

## Candidate pipeline

1. Match named ports and recording-site-identified constants.
2. Generate occurrence candidates from family, carrier, operation shape, and frontier evidence.
3. Infer candidate interiors by tape dependency closure.
4. Enumerate finite candidate combinations and test disjointness, coverage, ownership,
   progression, and occurrence constraints through `Match.accepts`.
5. Retain accepted candidates with proofs.
6. Quotient them by protected consequence signature.
7. Feed the single admitted class representative into `certifyCse`.

The first evidence plan targets the recorded `y = a * b + e` model. The engine and outcome
classifier are reusable; adapting the dielectric model requires its harvested evidence plan.

## Decisive controls

The qualification includes:

1. the existing undeclared constant;
2. distinct sources with equal values;
3. overlapping candidate interiors;
4. one operation assignable to two occurrences;
5. dependency reachability crossing an intended call boundary; and
6. repeated calls with identical family, carrier, inputs, and numerical result.

The last two controls decide the policy boundary. If the tape admits different protected
consequence classes with no tape-visible separator, the outcome is `AMBIGUOUS` and explicit
recorder scope evidence is necessary. Equivalent candidates remain one inferred class.

## End-to-end command

`pkc-certify-recording` emits:

```text
provenance graph + recorded tape
  -> INFERRED, AMBIGUOUS, or REJECTED
  -> checked Match.accepts or named obstruction
  -> checked CSE admission when inferred
  -> transported Match.accepts
  -> strong/weak bisimulation authority
  -> semantic-seal hypotheses and status
```

The command exposes `TapeSeal.semantic_seal` as conditional authority. It reports whether the
additional evaluation/denotation hypotheses are discharged; matching alone never claims the full
semantic seal.

## Deliverables and non-claims

Deliverables are Lean source, executable controls, a deterministic manifest, a one-command shell
entrypoint, documentation, and a clean GitHub Actions qualification on the fork.

This work does not prove dependency closure universally sufficient, infer metadata absent from the
tape, prove generic numerical denotation preservation for CSE, or verify scheduler, checkpoint,
CPU/GPU code generation, or machine code. It does not contact the original NASA/JPL repository.

