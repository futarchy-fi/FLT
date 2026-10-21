/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafClopenStabilization
public import FLT.Mazur.StableIdealPowerSupport

/-!
# Full ideal powers stabilize exactly on open closed support

The converse is checked on every original affine chart. Finite generation
of the stable coefficient ideal gives an idempotent equation locally;
these open supports glue. No reduced replacement of the ideal is made.
-/

@[expose] public noncomputable section
open AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.IdealSheafClopenStabilization
variable {X : Scheme.{0}} [IsLocallyNoetherian X] (I : X.IdealSheafData)

/-- Stationary full ideal powers force their entire closed support to be open. -/
theorem support_isOpen_of_pow_succ_eq (K : ℕ)
    (hK : I ^ (K + 1 + 1) = I ^ (K + 1)) :
    IsOpen (I.support : Set X) := by
  rw [IsOpenCover.isOpen_iff_coe_preimage (iSup_affineOpens_eq_top X)]
  intro U
  let _ := IsLocallyNoetherian.component_noetherian U
  have hp : (I.ideal U) ^ (K + 1 + 1) = (I.ideal U) ^ (K + 1) :=
    congrArg (fun L : X.IdealSheafData ↦ L.ideal U) hK
  have ho := (StableIdealPowerSupport.isClopen_zeroLocus_of_succ_eq
    (I.ideal U) K ((I.ideal U) ^ (K + 1)).fg_of_isNoetherianRing hp).2
  have he : Subtype.val ⁻¹' (I.support : Set X) =
      U.1.toSpecΓ ⁻¹' PrimeSpectrum.zeroLocus (I.ideal U : Set Γ(X, U.1)) := by
    rw [Scheme.Opens.toSpecΓ_preimage_zeroLocus]
    ext x
    exact Scheme.IdealSheafData.mem_support_iff_of_mem x.property
  rw [he]
  exact ho.preimage U.1.toSpecΓ.continuous

omit [IsLocallyNoetherian X] in
/-- On a Noetherian scheme, openness is the exact obstruction to full power stabilization. -/
theorem exists_stable_iff_support_isOpen [IsNoetherian X] :
    (∃ K : ℕ, ∀ l, K ≤ l → I ^ (l + 1) = I ^ (K + 1)) ↔
      IsOpen (I.support : Set X) := by
  constructor
  · rintro ⟨K, hK⟩
    exact support_isOpen_of_pow_succ_eq I K (hK (K + 1) (Nat.le_succ K))
  · exact exists_stable I

end FLT.Mazur.IdealSheafClopenStabilization
