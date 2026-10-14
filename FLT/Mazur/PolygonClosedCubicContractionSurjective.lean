/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonClosedCubicContractionFactorization
public import FLT.Mazur.WeierstrassGeometricIntegral

/-!
# The global one-gon comparison is proper and surjective

The specified closed cubic is integral. The original common identity open
therefore has dense image. Since that open factors through the constructed
proper global comparison, the latter covers the entire original closed cubic.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completeClosedFiberInclusion completePointToIntegralCubic

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "W" => completePointWeierstrassCurve K n h i
local notation "a" => closedPointContractionComparison K n h i
local notation "jC" => closedPointCubicIdentityInclusion K n h i
local notation "jN" => closedPointOneGonIdentityInclusion K n h i

/-- The actual Cartesian closed cubic is integral, including at its singular point. -/
theorem closedPointCubic_isIntegral : IsIntegral (closedPointCubicOver K n h i).left :=
  integralCurveFieldSquare_isIntegral W
    (completeClosedBase K ≫ (Spec (.of (PowerSeries K))).toSpecΓ)
    (pullback.fst _ _) (pullback.snd _ _) (IsPullback.of_hasPullback _ _)

/-- The global comparison is proper over the original residue field. -/
theorem closedPointContractionComparison_proper : IsProper (a).left := by
  let _ := PolygonProper.proper K 1 (by decide) (PolygonAtlas.normalization K 1)
    (PolygonAtlas.nodes K 1) (PolygonAtlas.isPushout K 1 (by decide))
  let _ : IsSeparated (closedPointCubicOver K n h i).hom := by
    change IsSeparated (pullback.snd (integralCurveStructure W) _)
    infer_instance
  have hp : IsProper ((a).left ≫ (closedPointCubicOver K n h i).hom) := by
    rw [Over.w]
    infer_instance
  exact IsProper.of_comp (a).left (closedPointCubicOver K n h i).hom

/-- The original common identity chart has dense image in the entire closed cubic. -/
theorem closedPointCubicIdentityInclusion_dense : DenseRange (jC) := by
  let _ : IsIntegral (completePointCubicBaseChange K n h (completeClosedBase K) i) :=
    closedPointCubic_isIntegral K n h i
  let _ : Nonempty (closedPointCommonIdentityOpen K n h i).toScheme :=
    ⟨closedPointCommonIdentityMarking K n h i default⟩
  exact (jC).isOpenMap.isOpen_range.dense (Set.range_nonempty (jC))

/-- The constructed proper global map reaches every point of the original closed cubic. -/
theorem closedPointContractionComparison_surjective : Surjective (a).left := by
  let _ := closedPointContractionComparison_proper K n h i
  have hd : DenseRange (a).left :=
    (closedPointCubicIdentityInclusion_dense K n h i).mono (by
      rintro _ ⟨x, rfl⟩
      exact ⟨(jN) x, congrArg (fun f ↦ f x)
        (closedPointContractionComparison_identity K n h i)⟩)
  constructor
  apply Set.range_eq_univ.mp
  rw [← ((a).left.isClosedMap.isClosed_range).closure_eq]
  exact hd.closure_eq

/-- The original closed-polygon comparison is surjective as well. -/
theorem closedPointToCubic_surjective : Surjective (closedPointToCubic K n h i) := by
  let _ : Surjective (closedPointContraction K n h i) :=
    PolygonOneGonContraction.contraction_surjective K n (by omega)
    (PolygonCyclicAtlas.normalization K n h) (PolygonCyclicAtlas.nodes K n h)
    (PolygonCyclicPushout.isPushout K n h (by omega)) i
  let _ := closedPointContractionComparison_surjective K n h i
  rw [← closedPointContractionComparison_fac]
  infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
