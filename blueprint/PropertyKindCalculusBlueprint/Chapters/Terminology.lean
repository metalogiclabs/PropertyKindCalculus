import Verso
import VersoManual
import VersoBlueprint
import PropertyKindCalculus
-- The dictionary cites declarations from every library layer, and the table directive
-- checks each one exists in *this* environment; so the chapter imports the layers the root
-- aggregator does not carry — the harvest (KindIncidence), the graph library, and the tape.
import PropertyKindCalculus.KindIncidence
import PropertyKindCalculus.Graph.Flow
import PropertyKindCalculus.Torch.Paradigm.TapeParity
import PropertyKindCalculus.Torch.Paradigm.TapeCse
import PropertyKindCalculus.Interaction
import PropertyKindCalculusBlueprint.TerminologyTable

open Verso.Genre
open Verso.Genre.Manual
open Informal
open PropertyKindCalculusBlueprint.TerminologyTable

#doc (Manual) "Terminology — the dictionary and the index" =>
%%%
tag := "terminology"
%%%

A reader who meets three phrases for one object concludes there are three objects. The
calculus names many objects that are close neighbors — several graphs, several tiers,
several boundaries — and a document that drifts between phrasings for any of them costs the
reader the very distinction the calculus was built to keep. So the vocabulary is managed the
way the requirements and the templates are: as data, rendered here, and gated.

Three rules govern it. *One defining site*: each term is defined by exactly one
`{deftech}` in the blueprint, under the section the dictionary names, and every other
mention is a `{tech}` link to that site or plain prose in the same words. *Canonical first,
short after*: a chapter, a module docstring, or a plan document uses the canonical phrase at
a concept's first mention and may use the sanctioned short form afterward. *Retired means
refused*: a phrasing the dictionary lists as retired fails the build's documentation gate
wherever the gate reads — every blueprint chapter and every root plan document — and is
counted in the library's own docstrings by a ratchet that may only fall.

The dictionary is `PropertyKindCalculus.Terminology.dictionary`. The table below is rendered
from it, sorted by canonical phrase; the *Defined in* column links to the section whose
prose explains the term, and the declarations column is checked, at blueprint build, against
the environment — a renamed declaration fails the render rather than surviving as a stale
name. A new concept gets its entry before its first use, so that the entry, the defining
site and the gate move together.

:::terminology_count
:::

# The dictionary

:::terminology_dictionary
:::

# Index

Every defining site also marks an index entry, and chapters may mark further entries at the
places a reader would look a term up. The index below is generated from those marks.

{theIndex}
