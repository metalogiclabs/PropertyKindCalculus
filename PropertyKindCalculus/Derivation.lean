/-
# Derivation — the conjunctive closure's induction principle, and homogeneity over any rule algebra

`Provenance.reachableFrom` is the conjunctive closure: a result is derivable once *all* its
operands are, and `wellFormed`'s central condition asks that every derived node, produced
port and exit lie in the closure of the sources (`known`). This module states the one
principle that closure supports and that two capstone theorems consume:

  * **soundness for closed predicates** (`reachableFrom_sound`) — a predicate that holds
    on the start set and is preserved by every occurrence, from operands to result, holds
    on everything the closure reaches. Its two immediate readings are `mem_known` — every
    known node is a source or the result of an occurrence, which is what the seal of a
    module (`Graph.Seal`) rests on — and `output_mem_known` / `derived_mem_known`, which
    unpack `sourcesReach`;
  * **dimensional homogeneity** (`homogeneity`) — stated over *any* rule algebra: a
    dimension type `D` and a rule per edge family from operand dimensions to result
    dimension. An assignment of dimensions to nodes is *homomorphic* along an occurrence
    when the rule carries the operands' dimensions to the result's. Two assignments that
    are homomorphic along every occurrence and agree on the sources agree on every known
    node — the dimension of every derived node and every output is determined by the
    sources' dimensions and the rules alone, along every path. The PhysLib instance, with
    the product/quotient/reciprocal/power/transcendental rules the coverage command
    evaluates, is `DimensionalHomogeneity` in the `Dimension` library; this module is
    prelude-only so the theorem's content is visible without it.

Everything here is structural recursion over lists, as the closure itself is.
-/

module

public import PropertyKindCalculus.Provenance

@[expose] public section Blanket

namespace PropertyKindCalculus.Provenance

variable {ν κ : Type} [BEq ν] [LawfulBEq ν] [BEq κ]

/-! ## One sweep, one occurrence at a time -/

omit [LawfulBEq ν] [BEq κ] in
theorem sweep_cons (o : Occurrence ν κ) (rest : List (Occurrence ν κ)) (ks : List ν) :
    sweep (o :: rest) ks = sweep rest (sweep [o] ks) := rfl

omit [LawfulBEq ν] [BEq κ] in
theorem sweep_singleton (o : Occurrence ν κ) (ks : List ν) :
    sweep [o] ks =
      if o.operands.all (fun oc => ks.contains oc.1) && !ks.contains o.result then
        ks ++ [o.result]
      else ks := rfl

/-! ## Soundness for closed predicates -/

omit [BEq κ] in
/-- A predicate closed under the conjunctive step — every operand satisfies it, so the
result does — and true on the start set is true on everything one sweep adds. -/
theorem sweep_sound (occs : List (Occurrence ν κ)) {P : ν → Prop}
    (hstep : ∀ o ∈ occs, (∀ oc ∈ o.operands, P oc.1) → P o.result) :
    ∀ ks : List ν, (∀ x ∈ ks, P x) → ∀ x ∈ sweep occs ks, P x := by
  induction occs with
  | nil => intro ks hks x hx; exact hks x (by simpa [sweep] using hx)
  | cons o rest ih =>
    intro ks hks x hx
    rw [sweep_cons] at hx
    refine ih (fun o' ho' => hstep o' (List.mem_cons_of_mem _ ho')) _ ?_ x hx
    intro y hy
    rw [sweep_singleton] at hy
    split at hy
    · rename_i hc
      rcases List.mem_append.mp hy with hy | hy
      · exact hks y hy
      · obtain rfl := List.mem_singleton.mp hy
        have hall := (Bool.and_eq_true .. ▸ hc).1
        exact hstep o (List.mem_cons_self ..) fun oc hoc =>
          hks _ (List.contains_iff_mem.mp (List.all_eq_true.mp hall oc hoc))
    · exact hks y hy

omit [BEq κ] in
/-- The same, over any number of sweeps. -/
theorem sweeps_sound (occs : List (Occurrence ν κ)) {P : ν → Prop}
    (hstep : ∀ o ∈ occs, (∀ oc ∈ o.operands, P oc.1) → P o.result) :
    ∀ (fuel : Nat) (ks : List ν), (∀ x ∈ ks, P x) → ∀ x ∈ sweeps occs fuel ks, P x
  | 0, ks, hks => fun x hx => hks x (by simpa [sweeps] using hx)
  | fuel + 1, ks, hks => by
    rw [sweeps]
    split
    · exact hks
    · exact sweeps_sound occs hstep fuel _ (sweep_sound occs hstep ks hks)

omit [BEq κ] in
/-- **The induction principle of the conjunctive closure.** A predicate true on the start
set and preserved along every occurrence — from all its operands to its result — is true on
everything derivable from the start set. -/
theorem reachableFrom_sound {g : Provenance ν κ} {start : List ν} {P : ν → Prop}
    (hstart : ∀ x ∈ start, P x)
    (hstep : ∀ o ∈ g.occurrences, (∀ oc ∈ o.operands, P oc.1) → P o.result) :
    ∀ x ∈ g.reachableFrom start, P x :=
  sweeps_sound g.occurrences hstep _ start hstart

omit [BEq κ] in
/-- A derivable node is in the start set or the result of some occurrence. -/
theorem mem_reachableFrom {g : Provenance ν κ} {start : List ν} {x : ν}
    (hx : x ∈ g.reachableFrom start) :
    x ∈ start ∨ ∃ o ∈ g.occurrences, o.result = x :=
  reachableFrom_sound (P := fun x => x ∈ start ∨ ∃ o ∈ g.occurrences, o.result = x)
    (fun _ hx => Or.inl hx) (fun o ho _ => Or.inr ⟨o, ho, rfl⟩) x hx

omit [BEq κ] in
/-- A known node — one the sources derive — is a source or the result of some occurrence. -/
theorem mem_known {g : Provenance ν κ} {x : ν} (hx : x ∈ g.known) :
    x ∈ g.sources ∨ ∃ o ∈ g.occurrences, o.result = x :=
  mem_reachableFrom hx

/-! ## What well-formedness places in the closure -/

omit [LawfulBEq ν] in
/-- Well-formedness, unpacked into its four clauses. -/
theorem WellFormed.clauses {g : Provenance ν κ} (h : g.WellFormed) :
    g.uniquelyDeclared = true ∧ g.occurrencesTyped = true ∧
      g.resultsAreDerivations = true ∧ g.sourcesReach = true := by
  have h' := h
  simp only [WellFormed, wellFormed, Bool.and_eq_true] at h'
  exact ⟨h'.1.1.1, h'.1.1.2, h'.1.2, h'.2⟩

/-- Every output of a well-formed graph — a produced port or an exit — is known. -/
theorem output_mem_known {g : Provenance ν κ} (h : g.WellFormed) {y : ν}
    (hy : y ∈ g.outputs) : y ∈ g.known := by
  have hsr := h.clauses.2.2.2
  simp only [sourcesReach, Bool.and_eq_true, List.all_eq_true] at hsr
  obtain ⟨⟨-, hports⟩, hexits⟩ := hsr
  rcases List.mem_append.mp hy with hy | hy
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hy
    obtain ⟨hp, hprod⟩ := List.mem_filter.mp hp
    have := hports p hp
    simp only [hprod, Bool.not_true, Bool.false_or] at this
    exact List.contains_iff_mem.mp this
  · exact List.contains_iff_mem.mp (hexits y hy)

/-- Every `derived` introduction of a well-formed graph is known: the anonymous-mint
clause, read as a membership. -/
theorem derived_mem_known {g : Provenance ν κ} (h : g.WellFormed) {i : Intro ν κ}
    (hi : i ∈ g.intros) (hd : i.tier = .derived) : i.node ∈ g.known := by
  have hsr := h.clauses.2.2.2
  simp only [sourcesReach, Bool.and_eq_true, List.all_eq_true] at hsr
  have := hsr.1.1 i hi
  simp only [hd, IntroTier.isDerived, Bool.not_true, Bool.false_or] at this
  exact List.contains_iff_mem.mp this

/-! ## Dimensional homogeneity over any rule algebra -/

/-- A rule algebra: for each edge family, the dimension its result carries given its
operands' dimensions in order, or `none` where the family imposes no rule or the operands
violate it (`exp` of a dimensioned quantity). The PhysLib instance is
`DimensionalHomogeneity.dimRule`; a `step` and a `select` have no rule here. -/
abbrev DimRule (D : Type) := EdgeFamily → List D → Option D

/-- The dimensions of a node list under an assignment, all of them or none. -/
def dimsOf {D : Type} (δ : ν → Option D) : List ν → Option (List D)
  | [] => some []
  | a :: l =>
    match δ a, dimsOf δ l with
    | some d, some ds => some (d :: ds)
    | _, _ => none

/-- An assignment of dimensions to nodes is *homomorphic* along an occurrence when every
operand is dimensioned, the family's rule applies to those dimensions, and the result
carries exactly the dimension the rule computes — the verdict the coverage command reports
as `[coherent]` for the edge, stated of one occurrence of the hypergraph. -/
def Homomorphic {D : Type} (rule : DimRule D) (δ : ν → Option D) (o : Occurrence ν κ) :
    Prop :=
  ∃ (ds : List D) (d : D),
    dimsOf δ (o.operands.map (·.1)) = some ds ∧ rule o.family ds = some d ∧
      δ o.result = some d

/-- The coverage verdict of one occurrence, executable: every operand dimensioned, the rule
defined on those dimensions, and the result carrying exactly the computed dimension. `true`
exactly when the assignment is homomorphic along the occurrence (`coherent_iff`), so an
instance pins the capstone's hypothesis with `decide` and a mutant is seen to fail it. -/
def coherent {D : Type} [BEq D] (rule : DimRule D) (δ : ν → Option D) (o : Occurrence ν κ) :
    Bool :=
  match dimsOf δ (o.operands.map (·.1)) with
  | some ds =>
    match rule o.family ds with
    | some d => δ o.result == some d
    | none => false
  | none => false

omit [BEq ν] [LawfulBEq ν] [BEq κ] in
theorem coherent_iff {D : Type} [BEq D] [LawfulBEq D] {rule : DimRule D} {δ : ν → Option D}
    {o : Occurrence ν κ} : coherent rule δ o = true ↔ Homomorphic rule δ o := by
  unfold coherent Homomorphic
  split
  · rename_i ds hds
    split
    · rename_i d hd
      constructor
      · intro h
        exact ⟨ds, d, hds, hd, by simpa using h⟩
      · rintro ⟨ds', d', hds', hd', hres⟩
        rw [hds] at hds'
        obtain rfl := Option.some.inj hds'
        rw [hd] at hd'
        obtain rfl := Option.some.inj hd'
        simpa using hres
    · rename_i hd
      constructor
      · intro h; simp at h
      · rintro ⟨ds', d', hds', hd', -⟩
        rw [hds] at hds'
        obtain rfl := Option.some.inj hds'
        rw [hd] at hd'
        exact absurd hd' (by simp)
  · rename_i hds
    constructor
    · intro h; simp at h
    · rintro ⟨ds', d', hds', -, -⟩
      rw [hds] at hds'
      exact absurd hds' (by simp)

/-- The declared assignment: each node's dimension is its declared kind's, where the kind
has one. What the coverage command evaluates its rules on. -/
def declaredDim {D : Type} (dimOf : κ → Option D) (g : Provenance ν κ) (n : ν) : Option D :=
  (g.kindOf? n).bind dimOf

omit [BEq ν] [LawfulBEq ν] in
theorem dimsOf_congr {D : Type} {δ₁ δ₂ : ν → Option D} :
    ∀ {l : List ν}, (∀ a ∈ l, δ₁ a = δ₂ a) → dimsOf δ₁ l = dimsOf δ₂ l
  | [], _ => rfl
  | a :: l, h => by
    have hl : dimsOf δ₁ l = dimsOf δ₂ l :=
      dimsOf_congr fun b hb => h b (List.mem_cons_of_mem _ hb)
    simp only [dimsOf, h a (List.mem_cons_self ..), hl]

omit [BEq κ] in
/-- **Dimensional homogeneity along the hypergraph.** Two assignments that are homomorphic
along every occurrence and agree on the sources agree on every known node: the dimension
of every derived node is determined by the sources' dimensions and the rules alone, along
every path of the hypergraph. -/
theorem homogeneity {D : Type} {g : Provenance ν κ} {rule : DimRule D}
    {δ₁ δ₂ : ν → Option D}
    (h₁ : ∀ o ∈ g.occurrences, Homomorphic rule δ₁ o)
    (h₂ : ∀ o ∈ g.occurrences, Homomorphic rule δ₂ o)
    (hsrc : ∀ s ∈ g.sources, δ₁ s = δ₂ s) :
    ∀ x ∈ g.known, δ₁ x = δ₂ x := by
  refine reachableFrom_sound (P := fun x => δ₁ x = δ₂ x) hsrc ?_
  intro o ho hops
  obtain ⟨ds₁, d₁, hds₁, hr₁, hres₁⟩ := h₁ o ho
  obtain ⟨ds₂, d₂, hds₂, hr₂, hres₂⟩ := h₂ o ho
  have hds : dimsOf δ₁ (o.operands.map (·.1)) = dimsOf δ₂ (o.operands.map (·.1)) :=
    dimsOf_congr fun a ha => by
      obtain ⟨oc, hoc, rfl⟩ := List.mem_map.mp ha
      exact hops oc hoc
  rw [hds₁, hds₂] at hds
  obtain rfl := Option.some.inj hds
  rw [hr₁] at hr₂
  obtain rfl := Option.some.inj hr₂
  rw [hres₁, hres₂]

/-- **The capstone form.** For a well-formed hypergraph whose declared dimensions are
homomorphic along every occurrence — the coverage verdict, per occurrence — any assignment
that is homomorphic along every occurrence and agrees with the declared one on the sources
agrees with it on every known node, hence on every derived node, produced port and exit:
the dimension of every output is the one the rules compute from the sources' dimensions. -/
theorem dimensional_homogeneity {D : Type} {g : Provenance ν κ} (hwf : g.WellFormed)
    {rule : DimRule D} {dimOf : κ → Option D}
    (hcov : ∀ o ∈ g.occurrences, Homomorphic rule (declaredDim dimOf g) o)
    {δ : ν → Option D} (hδ : ∀ o ∈ g.occurrences, Homomorphic rule δ o)
    (hsrc : ∀ s ∈ g.sources, δ s = declaredDim dimOf g s) :
    (∀ x ∈ g.known, δ x = declaredDim dimOf g x) ∧
      (∀ y ∈ g.outputs, δ y = declaredDim dimOf g y) ∧
      (∀ i ∈ g.intros, i.tier = .derived → δ i.node = declaredDim dimOf g i.node) := by
  have hk := homogeneity hδ hcov hsrc
  exact ⟨hk, fun y hy => hk y (output_mem_known hwf hy),
    fun i hi hd => hk i.node (derived_mem_known hwf hi hd)⟩

end PropertyKindCalculus.Provenance

end Blanket
