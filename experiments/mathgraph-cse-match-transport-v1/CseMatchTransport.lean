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

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Experiments.CseMatchTransport.transport_preserves_protected_partition' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms transport_preserves_protected_partition

/-- info: 'PropertyKindCalculus.Experiments.CseMatchTransport.equal_constants_do_not_respect_distinct_sources' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms equal_constants_do_not_respect_distinct_sources

end PropertyKindCalculus.Experiments.CseMatchTransport

end Blanket
