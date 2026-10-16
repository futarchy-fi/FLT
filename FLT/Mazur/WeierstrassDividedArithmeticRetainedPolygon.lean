/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedRetainedPolygonNaturality
public import FLT.Mazur.WeierstrassDividedArithmeticLabeledAtlasRestriction
public import FLT.Mazur.PolygonArithmeticStageRestriction

/-!
# Specific retained polygon maps on the original labeled arithmetic atlas

Both full retained arms map into the arithmetic (2k+3)-gon. These are actual
maps from the original labeled objects, and retain the original quotient arrows.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (H : ArithmeticAtlasCoefficients data) (m k : ℕ) (hk : k ≤ n)

/-- The specific polygon map from each full original retained arithmetic chart. -/
def arithmeticRetainedPolygonMap (a : Fin k) (b : Bool) :
    arithmeticLabeledAtlasObject hπ data H m k hk (.retained a b) ⟶
      (family R π m (2 * k + 3) (by omega)).left :=
  retainedPolygonMap (Quotient R π m) (parameter R π m) k a b

instance arithmeticRetainedPolygonMap_isOpenImmersion (a : Fin k) (b : Bool) :
    IsOpenImmersion (arithmeticRetainedPolygonMap hπ data H m k hk a b) :=
  retainedPolygonMap_isOpenImmersion _ _ _ _ _

omit [IsBezout R] in
/-- Every original retained consecutive edge commutes in the specified arithmetic polygon. -/
@[reassoc] theorem arithmeticRetainedPolygonMap_adjacent
    (a : ℕ) (ha : a + 1 < k) (b : Bool) :
    PolygonSmoothing.leftBranchOpen (Quotient R π m) (parameter R π m) ≫
      arithmeticRetainedPolygonMap hπ data H m k hk ⟨a, by omega⟩ b =
    PolygonSmoothing.precedingBranch (Quotient R π m) (parameter R π m) ≫
      arithmeticRetainedPolygonMap hπ data H m k hk ⟨a + 1, ha⟩ b :=
  retainedPolygonMap_adjacent _ _ _ _ _ _

omit [IsDomain R] [IsBezout R] in
/-- The original full node quotient is the explicit polygon ring coefficient map. -/
theorem arithmeticRetainedPolygonRestriction_eq :
    arithmeticPolygonNodeRestriction R π m =
      Spec.map (CommRingCat.ofHom (PolygonSmoothing.ringMap
        (restriction R π m).toRingHom (parameter R π (m + 1))
          (parameter R π m) (restriction_parameter R π m))) := by
  let _ := (restriction R π m).toRingHom.toAlgebra
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (PolygonSmoothing.ringMap_eq_coefficientMap
      (S := Quotient R π m) (parameter R π (m + 1))).symm

omit [IsBezout R] in
/-- The specific local comparison commutes with both original complete quotient diagrams. -/
@[reassoc] theorem arithmeticRetainedPolygonMap_restriction (a : Fin k) (b : Bool) :
    arithmeticLabeledAtlasRestriction hπ data H m k hk (.retained a b) ≫
      arithmeticRetainedPolygonMap hπ data H (m + 1) k hk a b =
    arithmeticRetainedPolygonMap hπ data H m k hk a b ≫
      stageRestriction R π m (2 * k + 3) (by omega) := by
  change arithmeticPolygonNodeRestriction R π m ≫ _ = _
  rw [arithmeticRetainedPolygonRestriction_eq]
  exact (retainedPolygonMap_parameterProjection (restriction R π m).toRingHom
    (parameter R π (m + 1)) (parameter R π m) (restriction_parameter R π m) k a b).symm

end FLT.Mazur.WeierstrassDividedDepth
