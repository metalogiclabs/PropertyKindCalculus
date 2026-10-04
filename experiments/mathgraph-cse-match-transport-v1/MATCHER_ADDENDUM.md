# Automatic matcher addendum

Prepared for Nicolas Rouquette and Xiaolan Xu  
Base PKC revision: `6d3da52c1db4a085ac7ea561dd8f125e7cdb0fc9`

## Finding

The manual-match gap is closed for PKC's recorded `y = a * b + e` worked model. The new matcher
constructs an accepted match from evidence at the recorder boundary, quotients accepted candidates
by the provenance consequences PKC protects, and returns `INFERRED`, `AMBIGUOUS`, or `REJECTED`.
The worked recording is `INFERRED / WARRANTED_BOUNDED` and agrees with the independently authored
18-vertex `rawMatch` on component ownership, occurrence boundaries, and operation ownership.

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

The decisive controls cover all requested boundaries:

| Mutation | Residual |
|---|---|
| undeclared anonymous leaf | `REJECTED: leaves-are-sources`, vertex 18 |
| missing constant recording site | `REJECTED: no-candidates` |
| overlapping realization interiors | `REJECTED: realized-topology, interiors-disjoint` |
| equal-valued constants owned by distinct sources under CSE | `REJECTED: component-ownership, component-multiplicity` |
| reordered but equivalent match tables | one `INFERRED` consequence class |
| repeated identical calls with crossed ownership | `AMBIGUOUS: component-ownership` |

## Exact scope

This result establishes that dependency-closure membership is sufficient for this checked model.
It also establishes a negative information result: when repeated calls have identical family,
carrier, inputs, operation shape, and result, the tape admits provenance-changing accepted matches.
No tape-only algorithm can recover the intended call identity in that case. Explicit recorder scope
evidence is therefore necessary for general intended-call recovery.

The next reusable contribution should therefore parameterize this working algorithm by harvested
metadata:

1. provenance node to recorder-name or recording-site selectors;
2. occurrence to family/carrier realization stages and root operations; and
3. explicit recorder scope markers for member-call ownership; and
4. consequence-classification of all accepted alternatives.

Instantiating that evidence plan for the dielectric model would convert the present vertical slice
into the presentation-ready end-to-end demonstration without overstating what the current tape
projection knows.

## Reproduction

```bash
experiments/mathgraph-cse-match-transport-v1/verify.sh
experiments/mathgraph-cse-match-transport-v1/pkc-certify-recording
```

The second command emits `PKC_CERTIFY_RECORDING_MANIFEST.yml`, including the pinned revision,
typed match outcome, bounded warrant, protected-consequence comparison, CSE decision, theorem
authority, scope separator, and explicitly remaining semantic-seal/denotation obligations.
