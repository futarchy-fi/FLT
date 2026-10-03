/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.PadicHodgeTheory.ComplexDeRhamGalois

/-! # Equivariance of completed theta and its filtration -/

@[expose] public noncomputable section
namespace PadicHodgeTheory
variable (p : ℕ) [Fact p.Prime]

/-- The actual residue identification intertwines the finite-quotient action. -/
theorem complexThetaResidueEquiv_equivariant (σ : PadicGalois p)
    (x : ComplexAinfInvertP p ⧸ ComplexDeRhamIdeal p) :
    complexThetaResidueEquiv p (Ideal.quotientMap (ComplexDeRhamIdeal p)
      (complexLocalizedGalois p σ) (complexLocalizedGalois_ideal p σ) x) =
      complexGalois p σ (complexThetaResidueEquiv p x) := by
  induction x using Quotient.inductionOn' with
  | h a => exact complexLocalizedTheta_equivariant p σ a

set_option backward.isDefEq.respectTransparency false in
/-- Completed theta intertwines the actual B_dR^+ and C_p actions. -/
theorem complexDeRhamTheta_equivariant (σ : PadicGalois p) (x : ComplexBDeRhamPlus p) :
    complexDeRhamTheta p (complexDeRhamGalois p σ x) =
      complexGalois p σ (complexDeRhamTheta p x) := by
  change complexThetaResidueEquiv p
    (AdicCompletion.evalOneₐ (ComplexDeRhamIdeal p)
      (adicRingMap _ _ _ x)) = _
  rw [adicRingMap_evalOne, complexThetaResidueEquiv_equivariant]
  rfl

/-- The actual completed parameter ideal is Galois stable. -/
theorem complexDeRhamGalois_ideal (σ : PadicGalois p) :
    Ideal.span {complexDeRhamParameter p} ≤
      (Ideal.span {complexDeRhamParameter p}).comap (complexDeRhamGalois p σ) := by
  rw [← complexDeRhamTheta_ker]
  intro x hx
  change complexDeRhamTheta p (complexDeRhamGalois p σ x) = 0
  rw [complexDeRhamTheta_equivariant, show complexDeRhamTheta p x = 0 from hx, map_zero]

/-- Every nonnegative filtration level is preserved in both directions. -/
theorem complexDeRhamGalois_mem_filtration_iff (σ : PadicGalois p)
    (x : ComplexBDeRhamPlus p) (n : ℕ) :
    complexDeRhamGalois p σ x ∈ Ideal.span {complexDeRhamParameter p} ^ n ↔
      x ∈ Ideal.span {complexDeRhamParameter p} ^ n := by
  exact adicRing_pow_mem_iff _ (complexDeRhamGalois p σ) (complexDeRhamGalois p σ⁻¹)
    (complexDeRhamGalois_ideal p σ) (complexDeRhamGalois_ideal p σ⁻¹)
    (fun y ↦ by rw [← complexDeRhamGalois_mul, inv_mul_cancel, complexDeRhamGalois_one]) n x

end PadicHodgeTheory
