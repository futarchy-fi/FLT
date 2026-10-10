/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteLineContractions
public import FLT.Mazur.PolygonNodePresentation

/-!
# Ordered horizontal line maps to the preceding node

The zero-slope line maps to the right node branch with parameter a₁U.
The other line maps to the left branch with parameter -a₁U. These are
identities of whole algebra maps, including the actual tensor contraction.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
local notation "K" => ResidueField R
local notation "a" => residue R W.a₁
local notation "f₁" => residueFiniteNodeLineMap hπ data D j hj hk0 hk 0 (by simp)
local notation "f₂" => residueFiniteNodeLineMap hπ data D j hj hk0 hk (-a) (by simp)

/-- The original zero-slope line kills the first normalized node coordinate. -/
theorem residueFiniteNodeFirstLine_x : (f₁) PolygonNodeLocalization.x = 0 := by
  rw [residueFiniteNodeLineMap_x, map_zero, mul_zero]

/-- Its other coordinate is the original line parameter scaled by a₁. -/
theorem residueFiniteNodeFirstLine_y : (f₁) PolygonNodeLocalization.y = C a * X := by
  rw [residueFiniteNodeLineMap_y, zero_add, mul_comm]

/-- The other original slope retains the negative scaling on the first node branch. -/
theorem residueFiniteNodeSecondLine_x : (f₂) PolygonNodeLocalization.x = C (-a) * X := by
  rw [residueFiniteNodeLineMap_x, mul_comm]

/-- The opposite line kills the second node coordinate. -/
theorem residueFiniteNodeSecondLine_y : (f₂) PolygonNodeLocalization.y = 0 := by
  rw [residueFiniteNodeLineMap_y, neg_add_cancel, map_zero, mul_zero]

/-- The complete first horizontal map is the scaled right branch of the preceding node. -/
theorem residueFiniteNodeFirstLine_eq : f₁ =
    (aeval (C a * X)).comp PolygonNodeEqualizer.second := by
  apply AlgHom.ext_of_adjoin_eq_top PolygonNodePresentation.a_adjoin
  intro z hz
  rcases hz with rfl | hz
  · rw [residueFiniteNodeFirstLine_x, AlgHom.comp_apply,
      PolygonNodeLocalization.second_x, map_zero]
  · rcases hz with rfl
    rw [residueFiniteNodeFirstLine_y, AlgHom.comp_apply,
      PolygonNodeLocalization.second_y, aeval_X]

/-- The complete opposite horizontal map is the negatively scaled left branch. -/
theorem residueFiniteNodeSecondLine_eq : f₂ =
    (aeval (C (-a) * X)).comp PolygonNodeEqualizer.first := by
  apply AlgHom.ext_of_adjoin_eq_top PolygonNodePresentation.a_adjoin
  intro z hz
  rcases hz with rfl | hz
  · rw [residueFiniteNodeSecondLine_x, AlgHom.comp_apply,
      PolygonNodeLocalization.first_x, aeval_X]
  · rcases hz with rfl
    rw [residueFiniteNodeSecondLine_y, AlgHom.comp_apply,
      PolygonNodeLocalization.first_y, map_zero]

open AlgebraicGeometry CategoryTheory

/-- On spectra the first line has the same ordered scaled branch factorization. -/
theorem residueFiniteNodeFirstLine_spec :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₁)) =
      Spec.map (CommRingCat.ofHom (aeval (C a * X)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (PolygonNodeEqualizer.second (R := K)).toRingHom) := by
  rw [residueFiniteNodeFirstLine_eq, ← Spec.map_comp]
  rfl

/-- On spectra the opposite line retains its original negative scale and left branch. -/
theorem residueFiniteNodeSecondLine_spec :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom f₂)) =
      Spec.map (CommRingCat.ofHom (aeval (C (-a) * X)).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (PolygonNodeEqualizer.first (R := K)).toRingHom) := by
  rw [residueFiniteNodeSecondLine_eq, ← Spec.map_comp]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
