# PKC Recording Matcher Implementation Plan

> **For agentic workers:** REQUIRED SUB-SKILL: Use superpowers:subagent-driven-development (recommended) or superpowers:executing-plans to implement this plan task-by-task. Steps use checkbox (`- [ ]`) syntax for tracking.

**Goal:** Build the full three-outcome, consequence-quotiented PKC recording matcher and compose its inferred result with the existing proof-carrying CSE gate.

**Architecture:** Add a reusable outcome/classification core around PKC's `Match.accepts`, then specialize finite candidate generation to the recorded complex model. Canonical protected consequence signatures quotient harmless table ambiguity; distinct signatures produce a concrete separator. The command-line layer renders the exact authority and semantic-seal residual boundary.

**Tech Stack:** Lean 4.34.0, PKC `TapeGraph`/`Match`, executable `#guard` controls, Bash, GitHub Actions.

**Spec:** `docs/superpowers/specs/2026-10-04-pkc-recording-matcher-design.md`

## Global Constraints

- Work only on `metalogiclabs/PropertyKindCalculus`; create no NASA/JPL PR, issue, comment, or notification.
- Preserve pinned PKC revision `6d3da52c1db4a085ac7ea561dd8f125e7cdb0fc9` in emitted evidence.
- Never identify anonymous constants by numerical equality; use recording-site evidence.
- Return `INFERRED` only with `Match.Accepts` proof authority.
- Treat semantic seal as conditional on its separate evaluation/denotation hypotheses.
- Forbid `sorry`, `admit`, and `native_decide` in the qualification.

## Review Focus

- Two accepted tables differing only by entry order must collapse to one consequence class.
- Two candidates changing component ownership must produce `AMBIGUOUS`, not `INFERRED`.
- An empty candidate set must return `REJECTED` with nonempty residuals and local conflict.
- A CSE rejection after successful inference must remain distinct from match rejection.
- A missing semantic-seal hypothesis must be printed as an obligation, never as discharged.

---

### Task 1: Protected consequence classifier

**Files:**
- Create: `experiments/mathgraph-cse-match-transport-v1/MatchInferenceCore.lean`
- Create: `experiments/mathgraph-cse-match-transport-v1/MatchInferenceCoreTests.lean`

**Interfaces:**
- Produces: `ProtectedConsequences`, `AcceptedCandidate`, `ConsequenceClass`, `AmbiguitySeparator`, `MatchObstruction`, `MatchInferenceOutcome`, `classifyCandidates`.

- [ ] Write guards for table-order equivalence, consequence-changing ambiguity, and empty rejection.
- [ ] Run the focused CI compile and confirm RED because the core module/API is absent.
- [ ] Implement canonical signatures, complete acceptance-clause residuals, local conflicts, grouping, and typed outcomes.
- [ ] Run focused CI and confirm all core guards pass.

### Task 2: Evidence-driven worked-model candidate generation

**Files:**
- Modify: `experiments/mathgraph-cse-match-transport-v1/RecordedMatchInference.lean`
- Modify: `experiments/mathgraph-cse-match-transport-v1/RecordedMatchInferenceTests.lean`

**Interfaces:**
- Consumes: Task 1 classifier.
- Produces: `WorkedModelEvidence`, `generateWorkedModelCandidates`, `inferWorkedModel`, `WarrantStatus.warrantedBounded`.

- [ ] Replace literal-control-only guards with outcome and consequence-equivalence guards.
- [ ] Add RED guards for undeclared constant, equal-valued distinct sources, overlap, dual occurrence assignment, boundary crossing, and repeated indistinguishable calls.
- [ ] Implement finite evidence-driven candidate generation and route every candidate through `classifyCandidates`.
- [ ] Confirm the worked recording is `INFERRED/WARRANTED_BOUNDED`, equivalent alternatives collapse, and provenance-changing alternatives are `AMBIGUOUS`.

### Task 3: End-to-end certification and semantic-seal boundary

**Files:**
- Replace: `experiments/mathgraph-cse-match-transport-v1/PkcMatchCertify.lean`
- Create: `experiments/mathgraph-cse-match-transport-v1/PKC_CERTIFY_RECORDING_MANIFEST.yml`
- Create: `experiments/mathgraph-cse-match-transport-v1/pkc-certify-recording`

**Interfaces:**
- Consumes: one inferred consequence class and `certifyCse`.
- Produces: deterministic recording manifest with match status, obstruction/separator, CSE status, theorem authority, and semantic-seal obligations.

- [ ] Add a RED golden-manifest comparison for `pkc-certify-recording`.
- [ ] Implement rendering of `INFERRED`, `AMBIGUOUS`, and `REJECTED`, with CSE only on `INFERRED`.
- [ ] Expose strong/weak bisimulation authority and semantic-seal obligations separately.
- [ ] Confirm the command output exactly matches the golden manifest.

### Task 4: Qualification, documentation, and fork-only publication

**Files:**
- Modify: `experiments/mathgraph-cse-match-transport-v1/verify.sh`
- Modify: `.github/workflows/mathgraph-matcher.yml`
- Modify: `experiments/mathgraph-cse-match-transport-v1/HANDOFF.md`
- Modify: `experiments/mathgraph-cse-match-transport-v1/REPORT.md`
- Modify: `experiments/mathgraph-cse-match-transport-v1/MATCHER_ADDENDUM.md`

**Interfaces:**
- Consumes: Tasks 1–3.
- Produces: one cold-run qualification and precise bounded claims.

- [ ] Extend verification to compile every new module, run every guard, compare the manifest, and scan forbidden proof placeholders.
- [ ] Document exact outcomes, the scope-necessity separator, and the dielectric evidence-plan residual.
- [ ] Run the complete workflow from the final commit and require zero failures.
- [ ] Publish only the Metalogic fork branch and update the existing ROS checkpoint with final evidence.
