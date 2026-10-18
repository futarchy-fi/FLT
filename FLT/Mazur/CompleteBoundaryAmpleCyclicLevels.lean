/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCompleteBoundarySubgroup
public import FLT.Mazur.PolygonCompleteBoundarySubgroupIso
public import FLT.Mazur.AmpleCyclicClassPresheaf

/-!
# Complete boundary families in the common ample cyclic moduli presheaf

The faithful one-gon smoothing and the complete polygons with at least two
components supply actual levels in the same moduli presheaf. Their restrictions
to every original boundary test are the retained closed levels. No finite-type
claim for a power-series coefficient spectrum is used.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CompleteBoundaryLevels
open GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) [NeZero n]
local notation "S" => Spec (CommRingCat.of (PowerSeries K))

/-- The faithful original complete one-gon gives an actual ample cyclic level. -/
def oneGonLevel
    (labels : Multiplicative (ZMod n) →*
      (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
    (hlabels : Function.Injective labels) : ampleCyclicLevels S n :=
  ⟨⟨OneGonSmoothing.completeGeneralizedCurve K,
    OneGonSmoothing.completeFiniteSubgroup K n labels hlabels⟩,
    OneGonSmoothing.completeFiniteSubgroup_isCyclic K n labels hlabels,
    OneGonSmoothing.completeFiniteSubgroup_isAmple K n labels hlabels⟩

/-- Every original complete polygon with at least two components gives the same level type. -/
def polygonLevel (h : 2 ≤ n) : ampleCyclicLevels S n :=
  ⟨⟨PolygonInfinitesimalStages.completeGeneralizedCurve K n h,
    PolygonInfinitesimalStages.completeOriginalFiniteSubgroup K n h⟩,
    PolygonInfinitesimalStages.completeOriginalFiniteSubgroup_isCyclic K n h,
    PolygonInfinitesimalStages.completeOriginalFiniteSubgroup_isAmple K n h⟩

/-- The unchanged original closed one-gon labels give an actual closed ample cyclic level. -/
def oneGonClosedLevel
    (labels : Multiplicative (ZMod n) →*
      (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
    (hlabels : Function.Injective labels) : ampleCyclicLevels (Spec (.of K)) n :=
  ⟨⟨_, OneGonSmoothing.completeClosedFiniteSubgroup K n labels hlabels⟩,
    OneGonSmoothing.completeClosedFiniteSubgroup_isCyclic K n labels hlabels,
    OneGonSmoothing.completeClosedFiniteSubgroup_isAmple K n labels hlabels⟩

/-- The original closed polygon subgroup gives an actual closed ample cyclic level. -/
def polygonClosedLevel (h : 2 ≤ n) : ampleCyclicLevels (Spec (.of K)) n :=
  ⟨⟨_, PolygonInfinitesimalStages.completeClosedFiniteSubgroup K n h⟩,
    PolygonInfinitesimalStages.completeClosedFiniteSubgroup_isCyclic K n h,
    PolygonInfinitesimalStages.completeClosedFiniteSubgroup_isAmple K n h⟩

/-- One-gon specialization agrees with its original closed level on every boundary test. -/
theorem oneGonLevel_boundary
    (labels : Multiplicative (ZMod n) →*
      (𝟙_ (Over (Spec (.of K))) ⟶ MultiplicativeGroupScheme.gm K))
    (hlabels : Function.Injective labels) {T : Scheme} (g : T ⟶ Spec (.of K)) :
    ampleCyclicClassesPullback
        (g ≫ Spec.map (CommRingCat.ofHom (PowerSeries.constantCoeff (R := K)))) n
        (Quotient.mk _ (oneGonLevel K n labels hlabels)) =
      Quotient.mk _ (ampleCyclicLevelsPullback g n (oneGonClosedLevel K n labels hlabels)) :=
  Quotient.sound ⟨OneGonSmoothing.completeBoundarySubgroupIso K n labels hlabels g⟩

/-- Polygon specialization agrees with its original closed level on every boundary test. -/
theorem polygonLevel_boundary (h : 2 ≤ n) {T : Scheme} (g : T ⟶ Spec (.of K)) :
    ampleCyclicClassesPullback (g ≫ PolygonInfinitesimalStages.completeClosedBase K) n
        (Quotient.mk _ (polygonLevel K n h)) =
      Quotient.mk _ (ampleCyclicLevelsPullback g n (polygonClosedLevel K n h)) :=
  Quotient.sound ⟨PolygonInfinitesimalStages.completeBoundarySubgroupIso K n h g⟩

end FLT.Mazur.CompleteBoundaryLevels
