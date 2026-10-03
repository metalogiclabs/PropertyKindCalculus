/-
# MathGraph qualification probe: the protected identity contract for CSE

This file factors the identity part of match transport through an arbitrary vertex remap.
It does not assume that numerical or structural equality is metrological equality.  Instead,
`CseRespectsMatch` states the three separations that compaction must preserve:

* components belonging to distinct provenance nodes;
* interiors belonging to distinct realized occurrences; and
* observable components versus silent realization interiors.

The transport theorem below proves that these are sufficient for the remapped match to
preserve those protected partitions.  Graph-topology preservation remains a separate
obligation before `Match.Accepts` can be transported in full.
-/

module

public import PropertyKindCalculus.Graph.Bisimulation

@[expose] public section Blanket

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm

namespace PropertyKindCalculus.Experiments.CseMatchTransport

/-- Map every tape vertex named by a match through a compaction remap. -/
def transportMatch (q : Nat → Nat) (m : Match ν) : Match ν where
  components := m.components.map fun e => (e.1, e.2.map q)
  realized := m.realized.map fun r => { r with interior := r.interior.map q }

/-- CSE preserves ownership of observable components. -/
def ComponentsSeparated [BEq ν] (m : Match ν) (q : Nat → Nat) : Prop :=
  ∀ ⦃a b u v⦄, u ∈ m.comps a → v ∈ m.comps b → q u = q v → a = b

/-- CSE preserves ownership of silent interior vertices. -/
def InteriorsSeparated (m : Match ν) (q : Nat → Nat) : Prop :=
  ∀ ⦃r s u v⦄, r ∈ m.realized → s ∈ m.realized →
    u ∈ r.interior → v ∈ s.interior → q u = q v → r = s

/-- CSE never identifies a silent interior vertex with an observable component. -/
def RolesSeparated [BEq ν] (m : Match ν) (q : Nat → Nat) : Prop :=
  ∀ ⦃r u a v⦄, r ∈ m.realized → u ∈ r.interior → v ∈ m.comps a → q u ≠ q v

/-- The non-topological, provenance-sensitive contract that a compaction remap must satisfy. -/
structure CseRespectsMatch [BEq ν] (m : Match ν) (q : Nat → Nat) : Prop where
  components : ComponentsSeparated m q
  interiors : InteriorsSeparated m q
  roles : RolesSeparated m q

private lemma find?_transport_components [BEq ν] (q : Nat → Nat)
    (cs : List (ν × List Nat)) (a : ν) :
    ((cs.map fun e => (e.1, e.2.map q)).find? fun e => e.1 == a) =
      (cs.find? fun e => e.1 == a).map fun e => (e.1, e.2.map q) := by
  induction cs with
  | nil => rfl
  | cons e cs ih =>
      simp only [List.map_cons, List.find?_cons]
      split <;> simp_all

lemma comps_transport [BEq ν] (q : Nat → Nat) (m : Match ν) (a : ν) :
    (transportMatch q m).comps a = (m.comps a).map q := by
  unfold Match.comps transportMatch
  rw [find?_transport_components]
  cases h : List.find? (fun e => e.1 == a) m.components <;> simp_all

lemma realized_transport_iff (q : Nat → Nat) (m : Match ν) (r' : Realized) :
    r' ∈ (transportMatch q m).realized ↔
      ∃ r ∈ m.realized, r' = { r with interior := r.interior.map q } := by
  simp [transportMatch, eq_comm]

/-- Component ownership in the transported match is exactly the source ownership protected
by `ComponentsSeparated`. -/
theorem transported_components_injective [BEq ν] (q : Nat → Nat) (m : Match ν)
    (h : ComponentsSeparated m q) ⦃a b z⦄
    (ha : z ∈ (transportMatch q m).comps a)
    (hb : z ∈ (transportMatch q m).comps b) : a = b := by
  rw [comps_transport] at ha hb
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ha
  obtain ⟨v, hv, huv⟩ := List.mem_map.mp hb
  exact h hu hv huv.symm

/-- Interior ownership in the transported match is protected by `InteriorsSeparated`. -/
theorem transported_interiors_injective (q : Nat → Nat) (m : Match ν)
    (h : InteriorsSeparated m q) ⦃r' s' z⦄
    (hr' : r' ∈ (transportMatch q m).realized)
    (hs' : s' ∈ (transportMatch q m).realized)
    (hzr : z ∈ r'.interior) (hzs : z ∈ s'.interior) : r' = s' := by
  obtain ⟨r, hr, rfl⟩ := (realized_transport_iff q m r').mp hr'
  obtain ⟨s, hs, rfl⟩ := (realized_transport_iff q m s').mp hs'
  simp only at hzr hzs
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hzr
  obtain ⟨v, hv, huv⟩ := List.mem_map.mp hzs
  have hrs : r = s := h hr hs hu hv huv.symm
  subst s
  rfl

/-- Observable and silent vertices remain disjoint after transport. -/
theorem transported_roles_disjoint [BEq ν] (q : Nat → Nat) (m : Match ν)
    (h : RolesSeparated m q) ⦃r' z a⦄
    (hr' : r' ∈ (transportMatch q m).realized)
    (hzi : z ∈ r'.interior)
    (hzc : z ∈ (transportMatch q m).comps a) : False := by
  obtain ⟨r, hr, rfl⟩ := (realized_transport_iff q m r').mp hr'
  simp only at hzi
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hzi
  rw [comps_transport] at hzc
  obtain ⟨v, hv, huv⟩ := List.mem_map.mp hzc
  exact h hr hu hv huv.symm

/-- The protected partition survives any remap satisfying `CseRespectsMatch`.  This is the
identity half of match transport; the remaining half is preservation of tape topology. -/
theorem transport_preserves_protected_partition [BEq ν] (q : Nat → Nat) (m : Match ν)
    (h : CseRespectsMatch m q) :
    (∀ ⦃a b z⦄, z ∈ (transportMatch q m).comps a →
      z ∈ (transportMatch q m).comps b → a = b) ∧
    (∀ ⦃r s z⦄, r ∈ (transportMatch q m).realized →
      s ∈ (transportMatch q m).realized → z ∈ r.interior → z ∈ s.interior → r = s) ∧
    (∀ ⦃r z a⦄, r ∈ (transportMatch q m).realized →
      z ∈ r.interior → z ∈ (transportMatch q m).comps a → False) := by
  exact ⟨transported_components_injective q m h.components,
    transported_interiors_injective q m h.interiors,
    transported_roles_disjoint q m h.roles⟩

/-! ## The existing equal-constant merge violates the contract when sources differ -/

def twoSourceMatch : Match Nat where
  components := [(0, [0]), (1, [1])]
  realized := []

def collapseTwo : Nat → Nat
  | 0 | 1 => 0
  | n => n

theorem equal_constants_do_not_respect_distinct_sources :
    ¬ CseRespectsMatch twoSourceMatch collapseTwo := by
  intro h
  have h0 : 0 ∈ twoSourceMatch.comps 0 := by decide
  have h1 : 1 ∈ twoSourceMatch.comps 1 := by decide
  have : (0 : Nat) = 1 := h.components h0 h1 rfl
  omega

/-! ## Full acceptance transport -/

/-- The evidence a tape quotient must carry in addition to source acceptance.  The identity
field records why the quotient is scientifically admissible; the remaining fields are the
target-side executable obligations that are not invariant under merely mapping vertex ids.

This is deliberately not an `Accepts` field.  The occurrence/key clauses are transported from
the source match below, so the certificate contains only the residual introduced by quotienting. -/
structure TapeQuotientCertificate [BEq ν] [BEq κ]
    (g : Provenance ν κ) (T' : TapeGraph) (m : Match ν) (q : Nat → Nat) : Prop where
  identity : CseRespectsMatch m q
  ordered : T'.ordered = true
  total : Match.totalOnNodes g T' (transportMatch q m) = true
  componentMultiplicity : Match.componentsDisjoint (transportMatch q m) = true
  leafSources : Match.leavesAreSources g T' (transportMatch q m) = true
  sourceLeaves : Match.sourcesAreLeaves g T' (transportMatch q m) = true
  realizedTopology :
    (transportMatch q m).realized.all (Match.realizedOk g T' (transportMatch q m)) = true
  interiorMultiplicity : Match.interiorsDisjoint (transportMatch q m) = true
  coverage : Match.covering g T' (transportMatch q m) = true

lemma uniqueKeys_transport [BEq ν] (q : Nat → Nat) (m : Match ν) :
    Match.uniqueKeys (transportMatch q m) = Match.uniqueKeys m := by
  simp [Match.uniqueKeys, transportMatch, Function.comp_def]

lemma keysDeclared_transport [BEq ν] [BEq κ] (g : Provenance ν κ)
    (q : Nat → Nat) (m : Match ν) :
    Match.keysDeclared g (transportMatch q m) = Match.keysDeclared g m := by
  simp [Match.keysDeclared, transportMatch, Function.comp_def]

lemma realizesAll_transport [BEq ν] [BEq κ] (g : Provenance ν κ)
    (q : Nat → Nat) (m : Match ν) :
    Match.realizesAll g (transportMatch q m) = Match.realizesAll g m := by
  simp [Match.realizesAll, transportMatch, Function.comp_def]

lemma realizedInGraph_transport [BEq ν] [BEq κ] (g : Provenance ν κ)
    (q : Nat → Nat) (m : Match ν) :
    Match.realizedInGraph g (transportMatch q m) = Match.realizedInGraph g m := by
  simp [Match.realizedInGraph, transportMatch, Function.comp_def]

/-- **Acceptance transport.** An accepted authored match remains accepted after a tape quotient
whenever the quotient carries the residual certificate above. -/
theorem transport_accepts [BEq ν] [BEq κ] {g : Provenance ν κ} {T T' : TapeGraph}
    {m : Match ν} {q : Nat → Nat} (old : m.Accepts g T)
    (cert : TapeQuotientCertificate g T' m q) :
    (transportMatch q m).Accepts g T' := by
  have h := Match.Acc.of_accepts old
  unfold Match.Accepts Match.accepts
  rw [cert.ordered, cert.total, uniqueKeys_transport q m, h.uniq,
    keysDeclared_transport g q m, h.keys, cert.componentMultiplicity,
    cert.leafSources, cert.sourceLeaves, cert.realizedTopology,
    cert.interiorMultiplicity, cert.coverage,
    realizesAll_transport g q m, h.all,
    realizedInGraph_transport g q m, h.inG]
  decide

/-- The protected partition promised by a quotient certificate. -/
theorem TapeQuotientCertificate.protectedPartition [BEq ν] [BEq κ]
    {g : Provenance ν κ} {T' : TapeGraph} {m : Match ν} {q : Nat → Nat}
    (cert : TapeQuotientCertificate g T' m q) :
    (∀ ⦃a b z⦄, z ∈ (transportMatch q m).comps a →
      z ∈ (transportMatch q m).comps b → a = b) ∧
    (∀ ⦃r s z⦄, r ∈ (transportMatch q m).realized →
      s ∈ (transportMatch q m).realized → z ∈ r.interior → z ∈ s.interior → r = s) ∧
    (∀ ⦃r z a⦄, r ∈ (transportMatch q m).realized →
      z ∈ r.interior → z ∈ (transportMatch q m).comps a → False) :=
  transport_preserves_protected_partition q m cert.identity

/-- Once acceptance transports, PKC's existing contraction theorem supplies the strong
bisimulation between the authored provenance graph and the contracted compacted tape. -/
theorem transport_strong_bisimulation [BEq ν] [LawfulBEq ν] [BEq κ]
    {g : Provenance ν κ} (hwf : g.WellFormed) {T T' : TapeGraph}
    {m : Match ν} {q : Nat → Nat} (old : m.Accepts g T)
    (cert : TapeQuotientCertificate g T' m q) :
    Cslib.LTS.IsBisimulation g.lts ((transportMatch q m).contracted g)
      (Match.obs (transportMatch q m)) :=
  Match.isBisimulation_contracted hwf
    (Match.Acc.of_accepts (transport_accepts old cert))

/-- The same certificate also recovers PKC's kind-transporting weak bisimulation against the
uncontracted compacted tape graph. -/
theorem transport_weak_bisimulation [BEq ν] [LawfulBEq ν] [BEq κ]
    {g : Provenance ν κ} (hwf : g.WellFormed) {T T' : TapeGraph}
    {m : Match ν} {q : Nat → Nat} (old : m.Accepts g T)
    (cert : TapeQuotientCertificate g T' m q) :
    Cslib.LTS.IsWeakBisimulation g.lts
      ((transportMatch q m).tapeLts g T') (Match.weak g (transportMatch q m)) :=
  Match.isWeakBisimulation_weak hwf
    (Match.Acc.of_accepts (transport_accepts old cert))

/-! ## Lawful-sharing control -/

/-- The remap observed in the executable equal-constant CSE control from the preceding
`mathgraph-cse-provenance-boundary-v1` qualification. -/
def repeatedSourceRemap : Nat → Nat
  | 0 | 1 => 0
  | n => n

def repeatedSource : Provenance Nat Nat where
  ports := []
  intros := [⟨0, 10, .attested "one calibration source"⟩]
  occurrences := []
  exits := []

/-- Both raw emissions belong to the same metrological source. -/
def repeatedSourceMatch : Match Nat where
  components := [(0, [0, 1])]
  realized := []

def repeatedSourceGraph : TapeGraph := ⟨[⟨none, []⟩, ⟨none, []⟩]⟩
def repeatedSourceGraphCse : TapeGraph := ⟨[⟨none, []⟩]⟩

lemma repeated_source_graph_size : repeatedSourceGraph.size = 2 := by decide
lemma repeated_source_graph_cse_size : repeatedSourceGraphCse.size = 1 := by decide
lemma repeated_source_remap_zero : repeatedSourceRemap 0 = 0 := by decide
lemma repeated_source_remap_one : repeatedSourceRemap 1 = 0 := by decide

lemma repeated_source_identity :
    CseRespectsMatch repeatedSourceMatch repeatedSourceRemap := by
  refine ⟨?_, ?_, ?_⟩
  · intro a b u v hu hv _
    have ha : a = 0 := by
      by_contra hne
      have hne' : 0 ≠ a := Ne.symm hne
      have hempty : repeatedSourceMatch.comps a = [] := by
        simp [repeatedSourceMatch, Match.comps, hne']
      rw [hempty] at hu
      simp at hu
    have hb : b = 0 := by
      by_contra hne
      have hne' : 0 ≠ b := Ne.symm hne
      have hempty : repeatedSourceMatch.comps b = [] := by
        simp [repeatedSourceMatch, Match.comps, hne']
      rw [hempty] at hv
      simp at hv
    omega
  · intro r s u v hr
    simp [repeatedSourceMatch] at hr
  · intro r u a v hr
    simp [repeatedSourceMatch] at hr

/-- The graph quotient corresponding to the executable equal-constant control carries the
complete certificate when both emissions are occurrences of one attested source. -/
theorem repeatedSourceCertificate : TapeQuotientCertificate repeatedSource
    repeatedSourceGraphCse repeatedSourceMatch repeatedSourceRemap where
  identity := repeated_source_identity
  ordered := by decide
  total := by decide
  componentMultiplicity := by decide
  leafSources := by decide
  sourceLeaves := by decide
  realizedTopology := by decide
  interiorMultiplicity := by decide
  coverage := by decide

lemma repeated_source_accepted :
    repeatedSourceMatch.Accepts repeatedSource repeatedSourceGraph := by decide

/-- The abstract quotient corresponding to the real `cseCompact` control transports the accepted
match when both emissions belong to one attested source. -/
theorem repeated_source_cse_accepts :
    (transportMatch repeatedSourceRemap repeatedSourceMatch).Accepts
      repeatedSource repeatedSourceGraphCse :=
  transport_accepts repeated_source_accepted repeatedSourceCertificate

lemma repeated_source_wellFormed : repeatedSource.WellFormed := by decide

/-- Non-vacuous strong-bisimulation witness after lawful compaction. -/
theorem repeated_source_strong_bisimulation :
    Cslib.LTS.IsBisimulation repeatedSource.lts
      ((transportMatch repeatedSourceRemap repeatedSourceMatch).contracted repeatedSource)
      (Match.obs (transportMatch repeatedSourceRemap repeatedSourceMatch)) :=
  transport_strong_bisimulation repeated_source_wellFormed
    repeated_source_accepted repeatedSourceCertificate

/-- Non-vacuous weak-bisimulation witness against the compacted tape graph. -/
theorem repeated_source_weak_bisimulation :
    Cslib.LTS.IsWeakBisimulation repeatedSource.lts
      ((transportMatch repeatedSourceRemap repeatedSourceMatch).tapeLts
        repeatedSource repeatedSourceGraphCse)
      (Match.weak repeatedSource (transportMatch repeatedSourceRemap repeatedSourceMatch)) :=
  transport_weak_bisimulation repeated_source_wellFormed
    repeated_source_accepted repeatedSourceCertificate

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Experiments.CseMatchTransport.transport_preserves_protected_partition' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transport_preserves_protected_partition

/-- info: 'PropertyKindCalculus.Experiments.CseMatchTransport.equal_constants_do_not_respect_distinct_sources' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms equal_constants_do_not_respect_distinct_sources

/-- info: 'PropertyKindCalculus.Experiments.CseMatchTransport.transport_accepts' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transport_accepts

/-- info: 'PropertyKindCalculus.Experiments.CseMatchTransport.transport_strong_bisimulation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transport_strong_bisimulation

/-- info: 'PropertyKindCalculus.Experiments.CseMatchTransport.transport_weak_bisimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transport_weak_bisimulation

/-- info: 'PropertyKindCalculus.Experiments.CseMatchTransport.repeated_source_cse_accepts' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeated_source_cse_accepts

/-- info: 'PropertyKindCalculus.Experiments.CseMatchTransport.repeated_source_strong_bisimulation' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeated_source_strong_bisimulation

/-- info: 'PropertyKindCalculus.Experiments.CseMatchTransport.repeated_source_weak_bisimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeated_source_weak_bisimulation

end PropertyKindCalculus.Experiments.CseMatchTransport

end Blanket
