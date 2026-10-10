/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteProper
public import FLT.Mazur.WeierstrassModificationAffineProper

/-!
# Every finite local modification is proper over the original affine cubic

Combine proper whole-exterior iteration with the actual first affine
contraction. This retains the previously constructed map to the original
projective cubic, without claiming that its missing exterior is present.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {k : ℕ} (d : Data W π k)

/-- The actual initial exterior whole maps to the original affine cubic. -/
def initialToAffine : (initialExterior d).whole ⟶
    Spec (.of (WeierstrassIntegralChart.Coordinate W 2)) :=
  (initialExteriorIso d).hom ≫ WeierstrassModificationX.affineContraction
    W (π ^ k) d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6

omit [IsDomain R] [IsBezout R] in
/-- The affine factorization retains the existing original-cubic contraction. -/
@[reassoc] theorem initialToAffine_toCurve :
    initialToAffine d ≫ WeierstrassIntegralChart.integralCurveChart W 2 = initialToCurve d := by
  rw [initialToAffine, Category.assoc, WeierstrassModificationX.affineContraction_toCurve]
  rfl

include hπ in
/-- The actual first whole scheme contracts properly to the original affine cubic. -/
theorem initialToAffine_isProper : IsProper (initialToAffine d) := by
  let _ := WeierstrassModificationReesCoordinates.affineContraction_isProper
    W (π ^ k) d.b3 d.b4 d.b6 d.factor3 d.factor4 d.factor6 (pow_ne_zero k hπ)
  unfold initialToAffine
  infer_instance

variable {start n : ℕ} (data : (i : Fin (n + 1)) → Data W π (start + i.val))

/-- The finite local construction retains a map to the same original affine cubic. -/
def finiteToAffine (j : ℕ) (hj : j ≤ n) : finiteModification hπ data j hj ⟶
    Spec (.of (WeierstrassIntegralChart.Coordinate W 2)) :=
  finiteContraction hπ data (initialExterior (data ⟨0, Nat.zero_lt_succ n⟩)) j hj ≫
    initialToAffine (data ⟨0, Nat.zero_lt_succ n⟩)

/-- All actual finite local modifications are proper over their original affine cubic. -/
theorem finiteToAffine_isProper (j : ℕ) (hj : j ≤ n) : IsProper (finiteToAffine hπ data j hj) := by
  let _ := initialToAffine_isProper hπ (data ⟨0, Nat.zero_lt_succ n⟩)
  exact finiteContraction_comp_isProper hπ data _ _ j hj

omit [IsBezout R] in
/-- The affine factorization is precisely the already constructed finite original contraction. -/
@[reassoc] theorem finiteToAffine_toCurve (j : ℕ) (hj : j ≤ n) :
    finiteToAffine hπ data j hj ≫ WeierstrassIntegralChart.integralCurveChart W 2 =
      finiteToCurve hπ data j hj := by
  rw [finiteToAffine, Category.assoc, initialToAffine_toCurve]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
