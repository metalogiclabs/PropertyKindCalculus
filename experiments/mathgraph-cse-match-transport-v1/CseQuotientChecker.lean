/-
# MathGraph executable admission checker for provenance-sensitive tape quotients

The checker reifies every field of `TapeQuotientCertificate` as independently inspectable
Boolean evidence.  Its soundness theorem is the bridge from an executable audit to PKC's
accepted-match and bisimulation capstones.
-/

module

public import CseMatchTransport
public meta import CseMatchTransport

@[expose] public section Blanket

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm

namespace PropertyKindCalculus.Experiments.CseQuotientChecker

open CseMatchTransport

/-! ## Finite, executable audit of the protected identity relation -/

/-- Check component ownership directly over the finite component table. -/
def componentsSeparatedB [BEq ν] (m : Match ν) (q : Nat → Nat) : Bool :=
  m.components.all fun ea => (m.comps ea.1).all fun u =>
    m.components.all fun eb => (m.comps eb.1).all fun v =>
      q u != q v || ea.1 == eb.1

/-- Check realization-interior ownership directly over the finite realization table. -/
def interiorsSeparatedB (m : Match ν) (q : Nat → Nat) : Bool :=
  m.realized.all fun r => r.interior.all fun u =>
    m.realized.all fun s => s.interior.all fun v =>
      q u != q v || decide (r = s)

/-- Check that no silent interior is identified with an observable component. -/
def rolesSeparatedB [BEq ν] (m : Match ν) (q : Nat → Nat) : Bool :=
  m.realized.all fun r => r.interior.all fun u =>
    m.components.all fun e => (m.comps e.1).all fun v => q u != q v

/-- Inspectable Boolean evidence for the three provenance-sensitive identity clauses. -/
structure CseIdentityAudit where
  components : Bool
  interiors : Bool
  roles : Bool
deriving DecidableEq, Repr, BEq

def CseIdentityAudit.passed (a : CseIdentityAudit) : Bool :=
  a.components && a.interiors && a.roles

def auditCseIdentity [BEq ν] (m : Match ν) (q : Nat → Nat) : CseIdentityAudit where
  components := componentsSeparatedB m q
  interiors := interiorsSeparatedB m q
  roles := rolesSeparatedB m q

private lemma componentsSeparatedB_sound [BEq ν] [LawfulBEq ν]
    {m : Match ν} {q : Nat → Nat} (h : componentsSeparatedB m q = true) :
    ComponentsSeparated m q := by
  simp only [componentsSeparatedB, List.all_eq_true] at h
  intro a b u v hu hv huv
  obtain ⟨ea, hea, ha, -⟩ := Match.exists_entry_of_mem_comps hu
  obtain ⟨eb, heb, hb, -⟩ := Match.exists_entry_of_mem_comps hv
  have hc := h ea hea u (by simpa [ha] using hu) eb heb v (by simpa [hb] using hv)
  simp [huv] at hc
  simpa [ha, hb] using hc

private lemma componentsSeparatedB_complete [BEq ν] [LawfulBEq ν]
    {m : Match ν} {q : Nat → Nat} (h : ComponentsSeparated m q) :
    componentsSeparatedB m q = true := by
  simp only [componentsSeparatedB, List.all_eq_true]
  intro ea hea u hu eb heb v hv
  by_cases huv : q u = q v
  · simp [huv, h hu hv huv]
  · simp [huv]

private lemma interiorsSeparatedB_sound {m : Match ν} {q : Nat → Nat}
    (h : interiorsSeparatedB m q = true) : InteriorsSeparated m q := by
  simp only [interiorsSeparatedB, List.all_eq_true] at h
  intro r s u v hr hs hu hv huv
  have hi := h r hr u hu s hs v hv
  simp [huv] at hi
  exact hi

private lemma interiorsSeparatedB_complete {m : Match ν} {q : Nat → Nat}
    (h : InteriorsSeparated m q) : interiorsSeparatedB m q = true := by
  simp only [interiorsSeparatedB, List.all_eq_true]
  intro r hr u hu s hs v hv
  by_cases huv : q u = q v
  · simp [huv, h hr hs hu hv huv]
  · simp [huv]

private lemma rolesSeparatedB_sound [BEq ν] [LawfulBEq ν] {m : Match ν} {q : Nat → Nat}
    (h : rolesSeparatedB m q = true) : RolesSeparated m q := by
  simp only [rolesSeparatedB, List.all_eq_true] at h
  intro r u a v hr hu hv
  obtain ⟨e, he, ha, -⟩ := Match.exists_entry_of_mem_comps hv
  have hd := h r hr u hu e he v (by simpa [ha] using hv)
  simpa [ha] using hd

private lemma rolesSeparatedB_complete [BEq ν] [LawfulBEq ν] {m : Match ν} {q : Nat → Nat}
    (h : RolesSeparated m q) : rolesSeparatedB m q = true := by
  simp only [rolesSeparatedB, List.all_eq_true]
  intro r hr u hu e he v hv
  exact bne_iff_ne.mpr (h hr hu hv)

theorem CseIdentityAudit.sound [BEq ν] [LawfulBEq ν] {m : Match ν} {q : Nat → Nat}
    (h : (auditCseIdentity m q).passed = true) : CseRespectsMatch m q := by
  simp only [CseIdentityAudit.passed, auditCseIdentity, Bool.and_eq_true] at h
  exact ⟨componentsSeparatedB_sound h.1.1, interiorsSeparatedB_sound h.1.2,
    rolesSeparatedB_sound h.2⟩

theorem CseIdentityAudit.complete [BEq ν] [LawfulBEq ν] {m : Match ν} {q : Nat → Nat}
    (h : CseRespectsMatch m q) : (auditCseIdentity m q).passed = true := by
  simp only [CseIdentityAudit.passed, auditCseIdentity, Bool.and_eq_true]
  exact ⟨⟨componentsSeparatedB_complete h.components,
    interiorsSeparatedB_complete h.interiors⟩, rolesSeparatedB_complete h.roles⟩

/-! ## Complete quotient audit -/

/-- The executable form of every residual field in `TapeQuotientCertificate`. -/
structure TapeQuotientAudit where
  identity : CseIdentityAudit
  ordered : Bool
  total : Bool
  componentMultiplicity : Bool
  leafSources : Bool
  sourceLeaves : Bool
  realizedTopology : Bool
  interiorMultiplicity : Bool
  coverage : Bool
deriving DecidableEq, Repr, BEq

def TapeQuotientAudit.passed (a : TapeQuotientAudit) : Bool :=
  a.identity.passed && a.ordered && a.total && a.componentMultiplicity &&
    a.leafSources && a.sourceLeaves && a.realizedTopology &&
    a.interiorMultiplicity && a.coverage

def auditTapeQuotient [BEq ν] [BEq κ] (g : Provenance ν κ) (T' : TapeGraph)
    (m : Match ν) (q : Nat → Nat) : TapeQuotientAudit :=
  let m' := transportMatch q m
  { identity := auditCseIdentity m q
    ordered := T'.ordered
    total := Match.totalOnNodes g T' m'
    componentMultiplicity := Match.componentsDisjoint m'
    leafSources := Match.leavesAreSources g T' m'
    sourceLeaves := Match.sourcesAreLeaves g T' m'
    realizedTopology := m'.realized.all (Match.realizedOk g T' m')
    interiorMultiplicity := Match.interiorsDisjoint m'
    coverage := Match.covering g T' m' }

theorem TapeQuotientAudit.sound [BEq ν] [LawfulBEq ν] [BEq κ]
    {g : Provenance ν κ} {T' : TapeGraph} {m : Match ν} {q : Nat → Nat}
    (h : (auditTapeQuotient g T' m q).passed = true) :
    TapeQuotientCertificate g T' m q := by
  simp only [TapeQuotientAudit.passed, auditTapeQuotient, Bool.and_eq_true] at h
  exact
    { identity := CseIdentityAudit.sound h.1.1.1.1.1.1.1.1
      ordered := h.1.1.1.1.1.1.1.2
      total := h.1.1.1.1.1.1.2
      componentMultiplicity := h.1.1.1.1.1.2
      leafSources := h.1.1.1.1.2
      sourceLeaves := h.1.1.1.2
      realizedTopology := h.1.1.2
      interiorMultiplicity := h.1.2
      coverage := h.2 }

theorem TapeQuotientAudit.complete [BEq ν] [LawfulBEq ν] [BEq κ]
    {g : Provenance ν κ} {T' : TapeGraph} {m : Match ν} {q : Nat → Nat}
    (cert : TapeQuotientCertificate g T' m q) :
    (auditTapeQuotient g T' m q).passed = true := by
  simp only [TapeQuotientAudit.passed, auditTapeQuotient, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨CseIdentityAudit.complete cert.identity, cert.ordered⟩, cert.total⟩,
    cert.componentMultiplicity⟩, cert.leafSources⟩, cert.sourceLeaves⟩,
    cert.realizedTopology⟩, cert.interiorMultiplicity⟩, cert.coverage⟩

theorem acceptance_of_audit [BEq ν] [LawfulBEq ν] [BEq κ]
    {g : Provenance ν κ} {T T' : TapeGraph} {m : Match ν} {q : Nat → Nat}
    (old : m.Accepts g T) (h : (auditTapeQuotient g T' m q).passed = true) :
    (transportMatch q m).Accepts g T' :=
  transport_accepts old (TapeQuotientAudit.sound h)

theorem strong_bisimulation_of_audit [BEq ν] [LawfulBEq ν] [BEq κ]
    {g : Provenance ν κ} (hwf : g.WellFormed) {T T' : TapeGraph}
    {m : Match ν} {q : Nat → Nat} (old : m.Accepts g T)
    (h : (auditTapeQuotient g T' m q).passed = true) :
    Cslib.LTS.IsBisimulation g.lts ((transportMatch q m).contracted g)
      (Match.obs (transportMatch q m)) :=
  transport_strong_bisimulation hwf old (TapeQuotientAudit.sound h)

theorem weak_bisimulation_of_audit [BEq ν] [LawfulBEq ν] [BEq κ]
    {g : Provenance ν κ} (hwf : g.WellFormed) {T T' : TapeGraph}
    {m : Match ν} {q : Nat → Nat} (old : m.Accepts g T)
    (h : (auditTapeQuotient g T' m q).passed = true) :
    Cslib.LTS.IsWeakBisimulation g.lts
      ((transportMatch q m).tapeLts g T') (Match.weak g (transportMatch q m)) :=
  transport_weak_bisimulation hwf old (TapeQuotientAudit.sound h)

/-! ## Positive and negative controls -/

#guard !(auditCseIdentity twoSourceMatch collapseTwo).passed
#guard (auditTapeQuotient repeatedSource repeatedSourceGraphCse
  repeatedSourceMatch repeatedSourceRemap).passed

def roleCollisionMatch : Match Nat where
  components := [(0, [0])]
  realized := [⟨0, [1]⟩]

#guard !(auditCseIdentity roleCollisionMatch collapseTwo).passed

def undeclaredLeafGraph : TapeGraph := ⟨[⟨none, []⟩, ⟨none, []⟩]⟩

#guard !(auditTapeQuotient repeatedSource undeclaredLeafGraph
  repeatedSourceMatch repeatedSourceRemap).passed

theorem repeated_source_audit_passes :
    (auditTapeQuotient repeatedSource repeatedSourceGraphCse
      repeatedSourceMatch repeatedSourceRemap).passed = true := by decide

theorem repeated_source_acceptance_from_audit :
    (transportMatch repeatedSourceRemap repeatedSourceMatch).Accepts
      repeatedSource repeatedSourceGraphCse :=
  acceptance_of_audit repeated_source_accepted repeated_source_audit_passes

theorem repeated_source_strong_from_audit :
    Cslib.LTS.IsBisimulation repeatedSource.lts
      ((transportMatch repeatedSourceRemap repeatedSourceMatch).contracted repeatedSource)
      (Match.obs (transportMatch repeatedSourceRemap repeatedSourceMatch)) :=
  strong_bisimulation_of_audit repeated_source_wellFormed repeated_source_accepted
    repeated_source_audit_passes

theorem repeated_source_weak_from_audit :
    Cslib.LTS.IsWeakBisimulation repeatedSource.lts
      ((transportMatch repeatedSourceRemap repeatedSourceMatch).tapeLts
        repeatedSource repeatedSourceGraphCse)
      (Match.weak repeatedSource (transportMatch repeatedSourceRemap repeatedSourceMatch)) :=
  weak_bisimulation_of_audit repeated_source_wellFormed repeated_source_accepted
    repeated_source_audit_passes

/-! ## Axiom profiles -/

/-- info: 'PropertyKindCalculus.Experiments.CseQuotientChecker.TapeQuotientAudit.sound' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms TapeQuotientAudit.sound

/-- info: 'PropertyKindCalculus.Experiments.CseQuotientChecker.acceptance_of_audit' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms acceptance_of_audit

/-- info: 'PropertyKindCalculus.Experiments.CseQuotientChecker.strong_bisimulation_of_audit' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms strong_bisimulation_of_audit

/-- info: 'PropertyKindCalculus.Experiments.CseQuotientChecker.weak_bisimulation_of_audit' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms weak_bisimulation_of_audit

/-- info: 'PropertyKindCalculus.Experiments.CseQuotientChecker.repeated_source_acceptance_from_audit' depends on axioms: [propext,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms repeated_source_acceptance_from_audit

end PropertyKindCalculus.Experiments.CseQuotientChecker

end Blanket
