# Handoff

This package now qualifies the PKC provenance--tape claim through the executable CSE boundary.

The headline chain is:

```text
actual 18-vertex recording
  -> dependency-closure match inference
  -> accepted match certificate
  -> actual cseCompact remap
  -> 14-vertex PKC control tape
  -> executable provenance-sensitive audit
  -> transported Match.accepts
  -> PKC strong and weak bisimulation theorems
```

The generic theorem `transport_accepts` proves that source acceptance plus a
`TapeQuotientCertificate` yields target acceptance. `TapeQuotientAudit.sound` and
`TapeQuotientAudit.complete` make that certificate an executable admission decision.
`recorded_cse_accepts`, `recorded_cse_strong_bisimulation`, and
`recorded_cse_weak_bisimulation` instantiate the chain on PKC's actual recorded complex model.

`CertifiedCseGate.lean` turns the chain into a typed execution boundary. `certifyCse` runs the
actual optimizer and returns either a `CertifiedCse` carrying proofs of source acceptance and the
quotient audit required by the target-acceptance/bisimulation theorems, or a `RejectedCse` carrying
the optimized artifact and all named failed clauses. `CertifiedCseControls.lean` checks the real
worked model and two adversarial runs.

The controls retain both sides of the scientific boundary: equal values from distinct declared
sources are rejected, while repeated emissions of one source are admitted. A separate role
collision and PKC's undeclared-leaf mutant prevent vacuous acceptance.

`RecordedMatchInference.lean` now closes the manual-match gap for this concrete worked recording.
It identifies named port emissions, keeps anonymous constants distinct by recording site, assigns
the complex-product and additive occurrences by dependency closure, and returns the match only
together with a proof of `Match.Accepts`. Accepted tables are compared by their protected
consequences—component ownership, occurrence boundaries, and operation ownership—not literal table
order. The worked-model result is `INFERRED / WARRANTED_BOUNDED` and has the same protected
consequences as the independently authored `rawMatch`.

The separator suite also answers PKC's scope-policy question. Reordered equivalent tables collapse
to one inferred class. An undeclared leaf, missing recording site, overlapping interiors, and the
equal-valued-distinct-source CSE mutation are rejected with named clauses. Two otherwise identical
member calls whose intended ownership is absent from the tape produce distinct accepted consequence
classes and therefore `AMBIGUOUS`. Dependency closure is sufficient for this model; explicit
recorder scopes are necessary for general recovery of intended call identity.

This is intentionally the smallest honest preemption of PKC's open matcher item. It demonstrates
that dependency-closure membership is sufficient for the recorded complex model and composes it
with the CSE gate. It does not claim that closure is sufficient for arbitrary programs: a generic
matcher still needs harvested port/recording-site metadata and a realization table indexed by
family and carrier.

Run:

```bash
experiments/mathgraph-cse-match-transport-v1/verify.sh
experiments/mathgraph-cse-match-transport-v1/pkc-certify all
experiments/mathgraph-cse-match-transport-v1/pkc-match-certify
experiments/mathgraph-cse-match-transport-v1/pkc-certify-recording
```

Read [`INDEPENDENT_REVIEW.md`](./INDEPENDENT_REVIEW.md) for the manager-facing assessment and
[`REPORT.md`](./REPORT.md) for the technical boundary. The completed concrete matcher and its
generalization boundary are summarized in [`MATCHER_ADDENDUM.md`](./MATCHER_ADDENDUM.md).

The concrete recorded-tape matcher is complete. `pkc-certify-recording` emits the match outcome,
bounded warrant, CSE decision, transported acceptance, bisimulation authority, and the still-open
semantic-seal hypotheses. The highest-leverage next step is to harvest the dielectric model's
metadata and explicit member-call scopes, then instantiate the same evidence plan. A numerical
denotation-preservation theorem for `cseCompact` remains independent work.
Strong bisimulation is established; literal graph
isomorphism, generic numerical denotation preservation by CSE, and correctness below the tape
(CUDA, scheduling, checkpoint/resume, machine code) are not claimed.
