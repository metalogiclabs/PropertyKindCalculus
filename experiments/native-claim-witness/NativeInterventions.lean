/- Native proof-dependency and fixed-proposition controls over pinned PKC. -/
module

public import CertifiedCseGate
public meta import Lean

@[expose] public section

namespace PropertyKindCalculus.Experiments.NativeInterventions

open PropertyKindCalculus PropertyKindCalculus.Paradigm
open PropertyKindCalculus.Experiments.CertifiedCseGate
open PropertyKindCalculus.Paradigm.TapeCodegen (ofTape)

/-- Fixed claim: the supplied certificate's source match is accepted. -/
theorem baseline {ν κ : Type} [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (c : CertifiedCse g m) :
    m.Accepts g (ofTape c.rawTape) :=
  c.sourceAccepted

/-- Same proposition, with the sourceAccepted supporting edge removed.
The certificate field and Boolean conjunction suffice directly. -/
theorem equivalentProof {ν κ : Type} [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (c : CertifiedCse g m) :
    m.Accepts g (ofTape c.rawTape) :=
by
  have h := c.checksPass
  simp only [Bool.and_eq_true] at h
  exact h.1

/-- Weaker conclusion, while retaining the same named PKC supporting edge.
The original fixed claim is not changed to match this declaration. -/
theorem weakenedConclusion {ν κ : Type} [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (c : CertifiedCse g m) :
    m.Accepts g (ofTape c.rawTape) ∨ True :=
  Or.inl c.sourceAccepted

-- Native positive consumers of the fixed requirement.
example {ν κ : Type} [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (c : CertifiedCse g m) :
    m.Accepts g (ofTape c.rawTape) := baseline c

example {ν κ : Type} [BEq ν] [BEq κ]
    {g : Provenance ν κ} {m : Match ν} (c : CertifiedCse g m) :
    m.Accepts g (ofTape c.rawTape) := equivalentProof c

#print axioms baseline
#print axioms equivalentProof
#print axioms weakenedConclusion

end PropertyKindCalculus.Experiments.NativeInterventions

open Lean in
private meta def proofConstants : Expr → List Name
  | .const n _ => [n]
  | .app f a => proofConstants f ++ proofConstants a
  | .lam _ t b _ => proofConstants t ++ proofConstants b
  | .forallE _ t b _ => proofConstants t ++ proofConstants b
  | .letE _ t v b _ => proofConstants t ++ proofConstants v ++ proofConstants b
  | .mdata _ b => proofConstants b
  | .proj _ _ b => proofConstants b
  | _ => []

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let some (.thmInfo b) := env.find? ``PropertyKindCalculus.Experiments.NativeInterventions.baseline
    | throwError "missing baseline theorem"
  let some (.thmInfo e) := env.find? ``PropertyKindCalculus.Experiments.NativeInterventions.equivalentProof
    | throwError "missing equivalent theorem"
  let some (.thmInfo w) := env.find? ``PropertyKindCalculus.Experiments.NativeInterventions.weakenedConclusion
    | throwError "missing weakened theorem"
  let edge := ``PropertyKindCalculus.Experiments.CertifiedCseGate.CertifiedCse.sourceAccepted
  unless (proofConstants b.value).contains edge do
    throwError "baseline supporting edge absent"
  if (proofConstants e.value).contains edge then
    throwError "equivalent proof did not delete the supporting edge"
  unless (proofConstants w.value).contains edge do
    throwError "weakened conclusion lost the selected supporting edge"
  unless b.type == e.type do
    throwError "positive theorem types differ"
  if b.type == w.type then
    throwError "weakened theorem incorrectly has the fixed type"
  logInfo "NATIVE_INTERVENTIONS: baseline_edge=PRESENT equivalent_edge=ABSENT weakened_edge=PRESENT"
  logInfo "FIXED_TYPE: baseline=MATCH equivalent=MATCH weakened=MISMATCH"
  logInfo "BOUNDARY: selected direct dependency only; not a complete FGM classification"
