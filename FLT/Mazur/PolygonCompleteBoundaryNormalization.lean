/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteBoundaryTranslation
public import FLT.Mazur.PolygonParameterProductNormalization

/-!
# Complete smoothing recovery on original normalization components

The complete product recovers each original component's marking and canonical
section. Varying translation retains the same map into the complete smoothing,
and the corresponding positive-line triangle commutes.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve PolygonParameterTranslation PolygonUniversalAction PolygonPinching
  PolygonMarkingBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase translationIso
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {T : Scheme} (g : T ⟶ Spec (.of K))
local notation "C" => PolygonCyclicAtlas.polygon K n h
local notation "p" => PolygonCyclicAtlas.normalization K n h
local notation "q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn

/-- The original parameter normalization component maps into the complete smoothing. -/
def completeBoundaryNormalizationMap (i : Fin n) :
    ((Over.pullback g).obj (component K)).left ⟶ exactVeroneseProj K n h :=
  ((Over.pullback g).map (componentι K n i ≫ p)).left ≫
    completeBoundaryParameterMap K n h g

/-- The complete product restricts to its original single marking on each component. -/
theorem completeMarkingDivisor_normalization (i : Fin n) :
    (completeMarkingDivisor K n h).comap (completeBoundaryNormalizationMap K n h g i) =
      ((PolygonMarkedSections.sectionMap K n p 1 i).ker.comap
        (componentι K n i ≫ p).left).comap (pullback.fst (component K).hom g) := by
  rw [completeBoundaryNormalizationMap, Scheme.IdealSheafData.comap_comp,
    completeMarkingDivisor_boundaryParameter,
    productMarkingIdeal_normalization K n hn p q hp]

/-- The complete positive line retains the original component marking line. -/
def completeBoundaryNormalizationLineIso (i : Fin n) :
    (Scheme.Modules.pullback (completeBoundaryNormalizationMap K n h g i)).obj
      (completeMarkingLine K n h) ≅ normalizationMarkingLine K n hn p q hp 1 i i g :=
  (Scheme.Modules.pullbackComp _ _).symm.app _ ≪≫
    (Scheme.Modules.pullback _).mapIso (completeBoundaryParameterLineIso K n h g) ≪≫
      productNormalizationLineIso K n hn p q hp g (fun _ ↦ 1) i

/-- Normalization recovery preserves the complete product's canonical section. -/
theorem completeBoundaryNormalizationLineIso_section (i : Fin n) :
    DivisorLineSectionCompatible (completeBoundaryNormalizationMap K n h g i)
      (completeMarkingDivisor_relativeCartier K n h).1
      (relativeCartierBaseChange (component K).hom g _
        (normalizationIdeal_relativeCartier K n hn p q hp 1 i i)).1
      (completeBoundaryNormalizationLineIso K n h g i) :=
  (completeBoundaryParameterLineIso_section K n h g).comp
    (productNormalizationLineIso_section K n hn p q hp g (fun _ ↦ 1) i)

variable (c : 𝟙_ (Over T) ⟶ (Over.pullback g).obj (G K n)) (i : Fin n)
local notation "ν" => Over.Hom.left
  (CategoryTheory.Functor.map (Over.pullback g) (componentι K n i ≫ p)) ≫
    Over.Hom.left (Iso.hom (translationIso K n hn p q hp g c))

/-- Translated normalization recovers the very same original complete-family map. -/
theorem completeBoundaryNormalizationMap_translation :
    (ν) ≫ completeMovedBoundaryMap K n h g c =
      completeBoundaryNormalizationMap K n h g i := by
  rw [Category.assoc, translation_completeMovedBoundaryMap]
  rfl

/-- The complete and translated normalization comparisons form the actual line triangle. -/
theorem completeBoundaryNormalizationLineIso_triangle :
    LinePullbackTriangle (ν) (completeMovedBoundaryMap K n h g c)
      (completeBoundaryNormalizationMap K n h g i)
      (completeBoundaryNormalizationMap_translation K n h g c i)
      (completeMovedBoundaryLineIso K n h g c)
      (movedProductNormalizationLineIso K n hn p q hp g c (fun _ ↦ 1) i)
      (completeBoundaryNormalizationLineIso K n h g i) :=
  divisorLineSectionCompatible_triangle _ _ _ _
    (completeMovedBoundaryLineIso_section K n h g c)
    (movedProductNormalizationLineIso_section K n hn p q hp g c (fun _ ↦ 1) i)
    (completeBoundaryNormalizationLineIso_section K n h g i)

end FLT.Mazur.PolygonInfinitesimalStages
