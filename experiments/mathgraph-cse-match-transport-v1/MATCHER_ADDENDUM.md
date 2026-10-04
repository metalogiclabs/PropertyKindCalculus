# Automatic matcher addendum

Prepared for Nicolas Rouquette and Xiaolan Xu  
Base PKC revision: `6d3da52c1db4a085ac7ea561dd8f125e7cdb0fc9`

## Finding

The manual-match gap is closed for PKC's recorded `y = a * b + e` worked model. The new matcher
reconstructs the independently authored 18-vertex `rawMatch` field-for-field from evidence at the
recorder boundary and returns it only with a proof that PKC's existing `Match.accepts` decision is
true.

The selected member-call policy is dependency closure. On this recording it identifies the four
complex-product partial products and the two observable product roots without explicit scope
markers. Port components are selected by recorded names. The anonymous complex constant is selected
by its two recording sites, never by numerical equality.

The actual execution path is now:

```text
record y = a * b + e
  -> project the 18-vertex tape graph
  -> infer an accepted provenance match
  -> run the actual cseCompact implementation
  -> check the provenance-sensitive quotient certificate
  -> recover optimized acceptance plus strong and weak bisimulation authority
```

## Controls

The positive run checks all of the following:

- the inferred source match equals the prior independently authored control;
- source `Match.accepts` holds;
- the actual 18-to-14 CSE run passes the complete quotient audit; and
- the existing optimized acceptance and bisimulation theorems are available.

Four mutations are rejected at stable boundaries:

| Mutation | Residual |
|---|---|
| extra named `a.re` emission | `source-evidence` |
| missing constant recording site | `source-evidence` |
| malformed complex-product operation | `realization-shape` |
| undeclared anonymous leaf | `match-acceptance` |

## Exact scope

This result establishes that dependency-closure membership is sufficient for this checked model.
It is not a universal matcher theorem. The projected `TapeGraph` intentionally contains operation
names and dependencies but not the provenance node names, constant recording-site identities, or a
family/carrier realization table required to infer arbitrary models without external evidence.

The next reusable contribution should therefore parameterize this working algorithm by harvested
metadata:

1. provenance node to recorder-name or recording-site selectors;
2. occurrence to family/carrier realization stages and root operations; and
3. an ambiguity policy that rejects non-unique assignments before `Match.accepts`.

Instantiating that evidence plan for the dielectric model would convert the present vertical slice
into the presentation-ready end-to-end demonstration without overstating what the current tape
projection knows.

## Reproduction

```bash
experiments/mathgraph-cse-match-transport-v1/verify.sh
experiments/mathgraph-cse-match-transport-v1/pkc-match-certify
```

The second command emits `AUTOMATIC_CERTIFICATION_MANIFEST.yml`, including the pinned revision,
matcher policy, independent-control equality, vertex counts, residuals, and theorem authority.
