/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXMiddleParameterPushout
public import FLT.Mazur.WeierstrassSuccessiveXMiddleSplitBranchCoordinates

/-!
# Original parameter branches specialize to the split node branches

The horizontal restriction is unchanged when the divided constant vanishes.
The conic restriction uses the full affine parameter isomorphism.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassSuccessiveX
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (c : K) (hc : c = 0)

/-- Both constructions retain exactly the same horizontal coordinate. -/
theorem middleLocalizedLineRestriction_eq_split :
    middleLocalizedLineRestriction c = middleSplitSecondRestriction c hc := by
  apply IsLocalization.algHom_ext (Submonoid.powers (middleNodeDenominator c))
  apply SuccessiveIncidence.hom_ext 0
  · exact (middleLocalizedLineRestriction_z c).trans
      (middleSplitSecondRestriction_z c hc).symm
  · exact (middleLocalizedLineRestriction_u c).trans
      (middleSplitSecondRestriction_u c hc).symm

/-- The horizontal branch does not change with the split source presentation. -/
@[reassoc] theorem middleParameterLineBranch_eq_split :
    middleParameterLineBranch c = middleNodeSecondBranch c hc := by
  rw [middleParameterLineBranch, middleNodeSecondBranch_eq_spec,
    middleLocalizedLineRestriction_eq_split c hc]

/-- The affine conic parameter recovers the whole split first restriction. -/
theorem middleLocalizedConicRestriction_eq_split :
    (conicZeroAffineEquiv c hc).toAlgHom.comp (middleLocalizedConicRestriction c) =
      middleSplitFirstRestriction c hc := by
  apply IsLocalization.algHom_ext (Submonoid.powers (middleNodeDenominator c))
  apply SuccessiveIncidence.hom_ext 0
  · change conicZeroAffineEquiv c hc
      (middleLocalizedConicRestriction c (middleNodeZ c)) = _
    rw [middleLocalizedConicRestriction_z]
    change conicZeroAffineEquiv c hc (algebraMap K[X] _ X) =
      middleSplitFirstRestriction c hc (middleNodeZ c)
    rw [conicZeroAffineEquiv_base, middleSplitFirstRestriction_z]
  · change conicZeroAffineEquiv c hc
      (middleLocalizedConicRestriction c (middleNodeU c)) =
        middleSplitFirstRestriction c hc (middleNodeU c)
    rw [middleLocalizedConicRestriction_u, map_zero, middleSplitFirstRestriction_u]

/-- The original conic parameter is precisely the split branch after source comparison. -/
@[reassoc] theorem middleParameterConicBranch_eq_split :
    (conicZeroAffineIso c hc).hom ≫ middleParameterConicBranch c =
      middleNodeFirstBranch c hc := by
  rw [middleParameterConicBranch, middleNodeFirstBranch_eq_spec]
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  exact congrArg (fun f : MiddleNodeOpen c →ₐ[K] K[X] =>
    Spec.map (CommRingCat.ofHom f.toRingHom))
      (middleLocalizedConicRestriction_eq_split c hc)

end FLT.Mazur.WeierstrassSuccessiveX
