/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteGlobalNegation
public import FLT.Mazur.WeierstrassDividedGenericCurve
public import FLT.Mazur.WeierstrassCoefficientNegation

/-!
# The original generic inverse inside each entire finite model

The original generic cubic is unchanged by contraction. Its pullback
uniqueness identifies the constructed global inverse with the inverse of
that same generic equation, keeping the original coefficient projection.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [Field K] [Algebra R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
local notation "N" => integralCurveNegation (W.map (algebraMap R K))
local notation "g" => finiteGlobalGenericCurve hπ data j hj hΔ

/-- The entire finite negative restricts to the inverse on the same original generic equation. -/
@[reassoc] theorem finiteGlobalGenericCurve_negation :
    g ≫ finiteGlobalNegation hπ data j hj = N ≫ g := by
  let H := finiteGlobalGenericCurve_contraction_isPullback hπ data j hj hΔ
  have he : N ≫ integralCoefficientMorphism W =
      (g ≫ finiteGlobalNegation hπ data j hj) ≫ finiteGlobalContraction hπ data j hj := by
    rw [Category.assoc, finiteGlobalNegation_contraction,
      finiteGlobalGenericCurve_contraction_assoc, integralCoefficientMorphism_negation]
  have h₁ := H.lift_fst N (g ≫ finiteGlobalNegation hπ data j hj) he
  have h₂ := H.lift_snd N (g ≫ finiteGlobalNegation hπ data j hj) he
  have hl : H.lift N (g ≫ finiteGlobalNegation hπ data j hj) he = N := by
    simpa only [Category.comp_id] using h₁
  rw [hl] at h₂
  exact h₂.symm

end FLT.Mazur.WeierstrassDividedDepth
