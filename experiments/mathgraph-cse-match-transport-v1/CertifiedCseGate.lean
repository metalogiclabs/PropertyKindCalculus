/-
# MathGraph proof-carrying CSE certification gate

This module turns the executable quotient audit into a result that either retains every
named failed obligation or carries the proof needed to recover PKC's acceptance and
bisimulation theorems.
-/

module

public import RecordedCseQualification
public meta import RecordedCseQualification

@[expose] public section Blanket

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm
open Spec TorchLean
open Runtime.Autograd (Tape)
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape)
open PropertyKindCalculus.Paradigm.TapeCSE (cseCompact)

namespace PropertyKindCalculus.Experiments.CertifiedCseGate

open CseQuotientChecker
open RecordedCseQualification

/-! ## Named residuals -/

/-- Every independently checked clause that may block quotient admission. -/
inductive TapeQuotientClause where
  | sourceMatchAcceptance
  | componentOwnership
  | interiorOwnership
  | roleSeparation
  | targetOrdered
  | targetTotal
  | componentMultiplicity
  | leavesAreSources
  | sourcesAreLeaves
  | realizedTopology
  | interiorMultiplicity
  | coverage
deriving DecidableEq, Repr, BEq

def TapeQuotientClause.label : TapeQuotientClause → String
  | .sourceMatchAcceptance => "source-match-acceptance"
  | .componentOwnership => "component-ownership"
  | .interiorOwnership => "interior-ownership"
  | .roleSeparation => "role-separation"
  | .targetOrdered => "target-ordered"
  | .targetTotal => "target-total"
  | .componentMultiplicity => "component-multiplicity"
  | .leavesAreSources => "leaves-are-sources"
  | .sourcesAreLeaves => "sources-are-leaves"
  | .realizedTopology => "realized-topology"
  | .interiorMultiplicity => "interior-multiplicity"
  | .coverage => "coverage"

def failedClause (clause : TapeQuotientClause) (ok : Bool) : List TapeQuotientClause :=
  if ok then [] else [clause]

/-- All failed clauses, in stable diagnostic order. -/
def tapeQuotientFailures (a : TapeQuotientAudit) : List TapeQuotientClause :=
  failedClause .componentOwnership a.identity.components ++
  failedClause .interiorOwnership a.identity.interiors ++
  failedClause .roleSeparation a.identity.roles ++
  failedClause .targetOrdered a.ordered ++
  failedClause .targetTotal a.total ++
  failedClause .componentMultiplicity a.componentMultiplicity ++
  failedClause .leavesAreSources a.leafSources ++
  failedClause .sourcesAreLeaves a.sourceLeaves ++
  failedClause .realizedTopology a.realizedTopology ++
  failedClause .interiorMultiplicity a.interiorMultiplicity ++
  failedClause .coverage a.coverage

theorem tapeQuotientFailures_eq_nil_iff (a : TapeQuotientAudit) :
    tapeQuotientFailures a = [] ↔ a.passed = true := by
  cases a with
  | mk i o t cm ls sl rt im c =>
    cases i with
    | mk co io ro =>
      cases co <;> cases io <;> cases ro <;> cases o <;> cases t <;> cases cm <;>
        cases ls <;> cases sl <;> cases rt <;> cases im <;> cases c <;>
        decide

/-! ## Proof-carrying result -/

/-- A successful run retains exactly the executable evidence required to recover the
accepted-match and bisimulation theorems. -/
structure CertifiedCse [BEq ν] [BEq κ] (g : Provenance ν κ) (m : Match ν) where
  rawTape : Tape Float
  compactTape : Tape Float
  remap : Array Nat
  checksPass :
    (m.accepts g (ofTape rawTape) &&
      (auditTapeQuotient g (ofTape compactTape) m (fun n => remap.getD n n)).passed) = true

def CertifiedCse.targetGraph [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (c : CertifiedCse g m) : TapeGraph :=
  ofTape c.compactTape

def CertifiedCse.vertexMap [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (c : CertifiedCse g m) : Nat → Nat :=
  fun n => c.remap.getD n n

theorem CertifiedCse.accepted [BEq ν] [LawfulBEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (c : CertifiedCse g m) :
    (CseMatchTransport.transportMatch c.vertexMap m).Accepts g c.targetGraph := by
  have h := c.checksPass
  simp only [Bool.and_eq_true] at h
  exact acceptance_of_audit h.1 h.2

theorem CertifiedCse.sourceAccepted [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (c : CertifiedCse g m) :
    m.Accepts g (ofTape c.rawTape) := by
  have h := c.checksPass
  simp only [Bool.and_eq_true] at h
  exact h.1

theorem CertifiedCse.strongBisimulation [BEq ν] [LawfulBEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν}
    (c : CertifiedCse g m) (hwf : g.WellFormed) :
    Cslib.LTS.IsBisimulation g.lts
      ((CseMatchTransport.transportMatch c.vertexMap m).contracted g)
      (Match.obs (CseMatchTransport.transportMatch c.vertexMap m)) := by
  have h := c.checksPass
  simp only [Bool.and_eq_true] at h
  exact strong_bisimulation_of_audit hwf h.1 h.2

theorem CertifiedCse.weakBisimulation [BEq ν] [LawfulBEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν}
    (c : CertifiedCse g m) (hwf : g.WellFormed) :
    Cslib.LTS.IsWeakBisimulation g.lts
      ((CseMatchTransport.transportMatch c.vertexMap m).tapeLts g c.targetGraph)
      (Match.weak g (CseMatchTransport.transportMatch c.vertexMap m)) := by
  have h := c.checksPass
  simp only [Bool.and_eq_true] at h
  exact weak_bisimulation_of_audit hwf h.1 h.2

/-- A rejected run retains the exact optimized artifact and audit that caused rejection. -/
structure RejectedCse [BEq ν] [BEq κ] (g : Provenance ν κ) (m : Match ν) where
  rawTape : Tape Float
  compactTape : Tape Float
  remap : Array Nat
  sourceAccepted : Bool
  sourceAccepted_eq : sourceAccepted = m.accepts g (ofTape rawTape)
  audit : TapeQuotientAudit
  audit_eq : audit = auditTapeQuotient g (ofTape compactTape) m (fun n => remap.getD n n)
  checksFailed : (sourceAccepted && audit.passed) = false

def RejectedCse.failures [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (r : RejectedCse g m) : List TapeQuotientClause :=
  failedClause .sourceMatchAcceptance r.sourceAccepted ++ tapeQuotientFailures r.audit

theorem certificationFailures_eq_nil_iff (sourceAccepted : Bool) (audit : TapeQuotientAudit) :
    failedClause .sourceMatchAcceptance sourceAccepted ++ tapeQuotientFailures audit = [] ↔
      (sourceAccepted && audit.passed) = true := by
  cases sourceAccepted <;> simp [failedClause, tapeQuotientFailures_eq_nil_iff]

theorem RejectedCse.failures_nonempty [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (r : RejectedCse g m) : r.failures ≠ [] := by
  intro h
  have hp := (certificationFailures_eq_nil_iff r.sourceAccepted r.audit).mp h
  have hf := r.checksFailed
  rw [hp] at hf
  contradiction

/-- The gate returns either a certificate with theorem authority or a complete named residual. -/
inductive CseCertification [BEq ν] [BEq κ] (g : Provenance ν κ) (m : Match ν) where
  | certified (result : CertifiedCse g m)
  | rejected (result : RejectedCse g m)

/-- Execute PKC's real `cseCompact`, audit the resulting quotient, and retain the proof of the
decision. This constructs no provenance match: the supplied source match remains sovereign. -/
def certifyCse [BEq ν] [BEq κ] (g : Provenance ν κ) (raw : Tape Float) (m : Match ν) :
    CseCertification g m :=
  let (compactTape, remap) := cseCompact raw
  let sourceAccepted := m.accepts g (ofTape raw)
  let audit := auditTapeQuotient g (ofTape compactTape) m (fun n => remap.getD n n)
  match h : sourceAccepted && audit.passed with
  | true => .certified { rawTape := raw, compactTape, remap, checksPass := h }
  | false => .rejected {
      rawTape := raw, compactTape, remap, sourceAccepted, sourceAccepted_eq := rfl,
      audit, audit_eq := rfl, checksFailed := h }

def CseCertification.isCertified [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} : CseCertification g m → Bool
  | .certified _ => true
  | .rejected _ => false

def CseCertification.failedClauses [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} : CseCertification g m → List TapeQuotientClause
  | .certified _ => []
  | .rejected r => r.failures

/-! ## Axiom profiles of the authority recovered from a successful run -/

/-- info: 'PropertyKindCalculus.Experiments.CertifiedCseGate.CertifiedCse.sourceAccepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CertifiedCse.sourceAccepted

/-- info: 'PropertyKindCalculus.Experiments.CertifiedCseGate.CertifiedCse.accepted' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CertifiedCse.accepted

/-- info: 'PropertyKindCalculus.Experiments.CertifiedCseGate.CertifiedCse.strongBisimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CertifiedCse.strongBisimulation

/-- info: 'PropertyKindCalculus.Experiments.CertifiedCseGate.CertifiedCse.weakBisimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms CertifiedCse.weakBisimulation

end PropertyKindCalculus.Experiments.CertifiedCseGate

end Blanket
