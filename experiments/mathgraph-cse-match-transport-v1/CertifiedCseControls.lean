/- MathGraph end-to-end positive and adversarial controls for the CSE gate. -/

module

public import CertifiedCseGate
public meta import CertifiedCseGate

@[expose] public section Blanket

open PropertyKindCalculus
open PropertyKindCalculus.Paradigm
open Spec TorchLean
open Runtime.Autograd (Tape TapeM)
open PropertyKindCalculus.Paradigm (TapeBuilder)

namespace PropertyKindCalculus.Experiments.CertifiedCseControls

open CertifiedCseGate
open RecordedCseQualification

/-! ## The actual PKC worked recording -/

def recordedCertification : Except String (CseCertification provenance rawMatch) :=
  recordRawAndCompact.map fun (raw, _, _, _, _, _, _) =>
    certifyCse provenance raw rawMatch

/-! ## Adversarial control 1: numerical equality erases distinct source identity -/

abbrev ScalarTapeBuilder := TapeBuilder Shape.scalar

def recordEqualConstants : Except String (Tape Float) := do
  let (_, raw) ← TapeM.run Tape.empty (do
    let _ ← (TapeBuilder.const 1.0 : ScalarTapeBuilder).run
    let _ ← (TapeBuilder.const 1.0 : ScalarTapeBuilder).run
    pure ())
  pure raw

def distinctSourceProvenance : Provenance Nat Nat where
  ports := []
  intros := [
    ⟨0, 10, .attested "kind 10 source"⟩,
    ⟨1, 20, .attested "kind 20 source"⟩]
  occurrences := []
  exits := []

def distinctSourceRawMatch : Match Nat where
  components := [(0, [0]), (1, [1])]
  realized := []

def distinctSourceCertification :
    Except String (CseCertification distinctSourceProvenance distinctSourceRawMatch) :=
  recordEqualConstants.map fun raw =>
    certifyCse distinctSourceProvenance raw distinctSourceRawMatch

/-! ## Adversarial control 2: an undeclared constant enters the output environment -/

def recordWorkedWithUndeclaredConstant : Except String (Tape Float) := do
  let (_, raw) ← TapeM.run Tape.empty (do
    let _ ← PropertyKindCalculus.Tests.TapeSeal.y.re.run
    let _ ← PropertyKindCalculus.Tests.TapeSeal.y.im.run
    let _ ← (TapeBuilder.const 42.0 : ScalarTapeBuilder).run
    pure ())
  pure raw

def undeclaredConstantCertification : Except String (CseCertification provenance rawMatch) :=
  recordWorkedWithUndeclaredConstant.map fun raw => certifyCse provenance raw rawMatch

-- Executable contracts: the actual worked recording certifies; both provenance attacks reject.
#guard recordEqualConstants.map (fun raw =>
  distinctSourceRawMatch.accepts distinctSourceProvenance
    (PropertyKindCalculus.Paradigm.TapeCodegen.ofTape raw)) == .ok true
#guard recordedCertification.map CseCertification.isCertified == .ok true
#guard distinctSourceCertification.map CseCertification.isCertified == .ok false
#guard distinctSourceCertification.map CseCertification.failedClauses ==
  .ok [.componentOwnership, .componentMultiplicity]
#guard undeclaredConstantCertification.map CseCertification.isCertified == .ok false
#guard undeclaredConstantCertification.map CseCertification.failedClauses ==
  .ok [.sourceMatchAcceptance, .leavesAreSources]

theorem recorded_gate_accepts {c : CertifiedCse provenance rawMatch}
    (_h : recordedCertification = .ok (.certified c)) :
    (CseMatchTransport.transportMatch c.vertexMap rawMatch).Accepts
      provenance c.targetGraph :=
  c.accepted

theorem recorded_gate_strong_bisimulation {c : CertifiedCse provenance rawMatch}
    (_h : recordedCertification = .ok (.certified c)) :
    Cslib.LTS.IsBisimulation provenance.lts
      ((CseMatchTransport.transportMatch c.vertexMap rawMatch).contracted provenance)
      (Match.obs (CseMatchTransport.transportMatch c.vertexMap rawMatch)) :=
  c.strongBisimulation provenance_wellFormed

theorem recorded_gate_weak_bisimulation {c : CertifiedCse provenance rawMatch}
    (_h : recordedCertification = .ok (.certified c)) :
    Cslib.LTS.IsWeakBisimulation provenance.lts
      ((CseMatchTransport.transportMatch c.vertexMap rawMatch).tapeLts
        provenance c.targetGraph)
      (Match.weak provenance (CseMatchTransport.transportMatch c.vertexMap rawMatch)) :=
  c.weakBisimulation provenance_wellFormed

/-! ## Pinned authority profiles -/

/-- info: 'PropertyKindCalculus.Experiments.CertifiedCseControls.recorded_gate_accepts' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recorded_gate_accepts

/-- info: 'PropertyKindCalculus.Experiments.CertifiedCseControls.recorded_gate_strong_bisimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recorded_gate_strong_bisimulation

/-- info: 'PropertyKindCalculus.Experiments.CertifiedCseControls.recorded_gate_weak_bisimulation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms recorded_gate_weak_bisimulation

end PropertyKindCalculus.Experiments.CertifiedCseControls

end Blanket
