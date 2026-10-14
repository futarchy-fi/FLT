/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCurveEulerIsomorphism
public import FLT.Mazur.PolygonClosedCubicEuler
public import FLT.Mazur.PolygonClosedCubicContractionIdentity

/-!
# The original closed cubic is the actual contracted one-gon

The constructed finite comparison is unchanged on a nonempty identity open.
The equal structure Euler characteristics eliminate its finite-support
cokernel, proving invertibility everywhere, especially at the pinched node.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "a" => closedPointContractionComparison K n h i
local notation "U" => completePointIdentityBaseChangeOpen K n h (completeClosedBase K) i

/-- The constructed global comparison is invertible on the whole original one-gon. -/
theorem closedPointContractionComparison_isIso : IsIso (a).left := by
  let _ := closedPointContractionComparison_finite K n h i
  let _ := closedPointContractionComparison_surjective K n h i
  let _ : IsIntegral (PolygonAtlas.polygon K 1).left := OneGonIntegral.integral K
  let _ := closedPointCubic_isIntegral K n h i
  let _ : IsProper (closedPointCubicOver K n h i).hom := by
    change IsProper (CategoryTheory.Limits.pullback.snd
      (WeierstrassIntegralChart.integralCurveStructure
        (completePointWeierstrassCurve K n h i)) _)
    infer_instance
  let _ := closedPointContractionComparison_identity_isIso K n h i
  apply finiteCurve_isIso_of_euler_eq (closedPointCubicOver K n h i).hom (a).left
    (PolygonDimension.atlas K 1).le U
  · exact ⟨completePointCubicChangedZero K n h (completeClosedBase K) i default,
      completePointIdentityBaseChangeOpen_zero_range K n h (completeClosedBase K) i
        ⟨default, rfl⟩⟩
  · exact closedPointContractionComparison_euler K n h i

/-- The entire specified cubic is canonically the actual contracted one-gon. -/
def closedPointContractionCubicIso :
    (PolygonAtlas.polygon K 1).left ≅ (closedPointCubicOver K n h i).left := by
  let _ := closedPointContractionComparison_isIso K n h i
  exact asIso (a).left

/-- The original closed-polygon cubic map is exactly its contraction followed by this iso. -/
@[reassoc] theorem closedPointContractionCubicIso_fac :
    closedPointContraction K n h i ≫ (closedPointContractionCubicIso K n h i).hom =
      closedPointToCubic K n h i := closedPointContractionComparison_fac K n h i

/-- The global inverse identifies the original cubic map with the actual contraction. -/
@[reassoc] theorem closedPointContractionCubicIso_inverse_fac :
    closedPointToCubic K n h i ≫ (closedPointContractionCubicIso K n h i).inv =
      closedPointContraction K n h i := by
  rw [← closedPointContractionCubicIso_fac, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The entire comparison retains the original residue-field structure map. -/
@[reassoc] theorem closedPointContractionCubicIso_over :
    (closedPointContractionCubicIso K n h i).hom ≫ (closedPointCubicOver K n h i).hom =
      (PolygonAtlas.polygon K 1).hom := Over.w (a)

/-- The original marking is preserved by the global isomorphism. -/
@[reassoc] theorem closedPointContractionCubicIso_marking :
    PolygonMarkedSections.sectionMap K 1 (PolygonAtlas.normalization K 1) 1 0 ≫
      (closedPointContractionCubicIso K n h i).hom =
        completePointCubicChangedZero K n h (completeClosedBase K) i :=
  closedPointContractionComparison_marking K n h i

end FLT.Mazur.PolygonInfinitesimalStages
