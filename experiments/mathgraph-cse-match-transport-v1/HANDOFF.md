# Handoff

This package now qualifies the PKC provenance--tape claim through the executable CSE boundary.

The headline chain is:

```text
actual 18-vertex recording
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

Run:

```bash
experiments/mathgraph-cse-match-transport-v1/verify.sh
experiments/mathgraph-cse-match-transport-v1/pkc-certify all
```

Read [`INDEPENDENT_REVIEW.md`](./INDEPENDENT_REVIEW.md) for the manager-facing assessment and
[`REPORT.md`](./REPORT.md) for the technical boundary.

The proof-producing wrapper is complete. The highest-leverage next step is the generic
recorded-tape matcher already identified in PKC, followed independently by a numerical
denotation-preservation theorem for `cseCompact`. A universal loop theorem remains separate work.
Strong bisimulation is established; literal graph
isomorphism, generic numerical denotation preservation by CSE, and correctness below the tape
(CUDA, scheduling, checkpoint/resume, machine code) are not claimed.
