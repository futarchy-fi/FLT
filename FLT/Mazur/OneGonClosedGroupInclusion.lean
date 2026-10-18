/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonZeroTorusComparison
public import FLT.Mazur.OneGonNodalCoefficientGroupProjection

/-!
# The closed smooth-group comparison retains the whole-curve embedding

The inverse smooth-group comparison is the original Laurent parametrization
followed by the original coefficient map, with all equation transports retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.OneGonSmoothing
open WeierstrassIntegralChart WeierstrassDividedDepth
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

attribute [local irreducible] originalSmoothCoefficientGroupIso integralSmoothSplitNodalTorusIso
variable (K : Type) [Field K]
/-- The closed coefficient algebra uses the constant coefficient homomorphism. -/
local instance closedCoefficientAlgebra : Algebra (PowerSeries K) K :=
  (PowerSeries.constantCoeff (R := K)).toAlgebra
local notation "t" => (PowerSeries.X : PowerSeries K)
local notation "c" => Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))

/-- The closed coefficient equation is exactly the zero-parameter family equation. -/
theorem completeClosed_zeroEquation :
    (equation (t)).map PowerSeries.constantCoeff = equation (0 : K) :=
  completeClosed_equation K

/-- Forgetting the closed group comparison retains its underlying inverse map. -/
theorem completeClosedGroupTorusOverIso_inv_left :
    (completeClosedGroupTorusOverIso K).inv.left =
      (completeClosedGroupTorusIso K).inv.hom.hom.hom.left := rfl

/-- The closed inverse retains the three original smooth coefficient factors. -/
theorem completeClosedGroupTorusIso_inv_projection :
    (completeClosedGroupTorusIso K).inv.hom.hom.hom.left =
      (splitNodalRelativeSmoothOverIso (-1 : Kˣ)).hom.left ≫
        eqToHom (congrArg (fun V => (integralSmoothOpen V).toScheme)
          (completeClosed_equation K).symm) ≫
            (originalSmoothCoefficientIso K (equation (t))).hom := by
  exact nodalCoefficientGroupIso_projection_of_eq K (equation (t)) (-1 : Kˣ)
    (completeClosed_equation K) (completeClosedGroupTorusIso K)
    (completeClosedGroupTorusIso_def K)

/-- The closed group inverse retains the actual projection into the original complete cubic. -/
@[reassoc] theorem completeClosedGroupTorusIso_inv_inclusion :
    (completeClosedGroupTorusOverIso K).inv.left ≫
      pullback.fst (relativeGroup (t)).X.hom (c) ≫
        (relativeGroupInclusion (t)).left =
    (splitNodalRelativeSmoothOverIso (-1 : Kˣ)).hom.left ≫
      (relativeGroupInclusion (0 : K)).left ≫
        eqToHom (congrArg integralCurve (completeClosed_zeroEquation K).symm) ≫
          integralCoefficientMorphism (S := K) (equation (t)) := by
  rw [completeClosedGroupTorusOverIso_inv_left]
  exact nodalCoefficientGroupIso_inclusion_of_eq K (equation (t)) (-1 : Kˣ)
    (completeClosed_equation K) (completeClosedGroupTorusIso K)
    (completeClosedGroupTorusIso_def K)

/-- The actual closed curve comparison uses the same equation transport as its smooth group. -/
theorem powerSeriesClosedFiberIso_fst :
    (powerSeriesClosedFiberIso K).hom ≫ pullback.fst (family (t)).hom (c) =
      (zeroFiberIso K).hom ≫
        eqToHom (congrArg integralCurve (completeClosed_zeroEquation K).symm) ≫
          integralCoefficientMorphism (S := K) (equation (t)) := by
  exact zeroParameterFiberIso_equation_fst K (t) PowerSeries.constantCoeff_X


/-- The entire closed comparison restricts to the original torus after coordinate inversion. -/
@[reassoc] theorem powerSeriesClosedFiberIso_torus_fst :
    OneGonGluing.torus K ≫ (powerSeriesClosedFiberIso K).hom ≫
      pullback.fst (family (t)).hom (c) =
    ι[MultiplicativeGroupScheme.gm K].left ≫ (completeClosedGroupTorusOverIso K).inv.left ≫
      pullback.fst (relativeGroup (t)).X.hom (c) ≫
        (relativeGroupInclusion (t)).left := by
  rw [powerSeriesClosedFiberIso_fst, torus_zeroFiberIso_group_assoc,
    completeClosedGroupTorusIso_inv_inclusion]

end FLT.Mazur.OneGonSmoothing
