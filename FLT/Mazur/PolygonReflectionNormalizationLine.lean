/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonMarkingNormalizationLine
public import FLT.Mazur.PolygonTranslationMarkingLine
public import FLT.Mazur.PolygonReflectionMarkingLine
public import FLT.Mazur.TensorPowerPullbackSquare

/-!
# Full relabeling on every actual normalization component

The canonical translation and reflection comparisons commute with restriction
to every projective normalization component, including the unmarked components.
These are equalities of actual isomorphisms in every tensor degree.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonMarkedSections
open PolygonPinching PolygonSinglePointLineNormalization FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] polygonReflection PolygonActionTranslation.translation
  tensorPowerPullbackComparison divisorLinePullbackIsoOfEq
variable (K : Type) [Field K] (n : ℕ) [NeZero n] (hn : 0 < n)
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (h : IsPushout (toComponents K n hn) (toNodes K n) p q)

/-- The actual reflection square on each complete normalization component. -/
theorem reflection_normalization_left (i : Fin n) :
    (componentι K n i ≫ p).left ≫ (polygonReflection K hn p q h).left =
      ProjectiveLine.endpointReversal K ≫ (componentι K n (reflectIndex i) ≫ p).left :=
  congrArg Over.Hom.left (componentι_polygonReflection K hn p q h i)

include h in
/-- The original Cartier marking ideals agree across the normalization square. -/
theorem reflection_normalization_ideal (a : Kˣ) (j i : Fin n) :
    ((sectionMap K n p (a⁻¹) (reflectIndex j)).ker.comap
      (componentι K n (reflectIndex i) ≫ p).left).comap (ProjectiveLine.endpointReversal K) =
        (sectionMap K n p a j).ker.comap (componentι K n i ≫ p).left := by
  rw [← Scheme.IdealSheafData.comap_comp,
    ← reflection_normalization_left K n hn p q h i,
    Scheme.IdealSheafData.comap_comp, section_reflection_ideal K n hn p q h a j]

/-- The canonical reflection comparison on each original normalization component. -/
irreducible_def reflectionNormalizationLineIso (a : Kˣ) (j i : Fin n) :
    (Scheme.Modules.pullback (ProjectiveLine.endpointReversal K)).obj
      (divisorLineBundle _
        (normalizationIdeal_cartier K n hn p q h (a⁻¹) (reflectIndex j) (reflectIndex i))) ≅
      divisorLineBundle _ (normalizationIdeal_cartier K n hn p q h a j i) := by
  let ht := normalizationIdeal_cartier K n hn p q h (a⁻¹) (reflectIndex j) (reflectIndex i)
  let hs := normalizationIdeal_cartier K n hn p q h a j i
  let w := reflection_normalization_ideal K n hn p q h a j i
  let _ := idealModulePullbackHom_isIso_of_cartier
    (ProjectiveLine.endpointReversal K) ht (w.symm ▸ hs)
  exact divisorLinePullbackIsoOfEq _ ht hs w

/-- Every normalization comparison retains the actual canonical marking section. -/
theorem reflectionNormalizationLineIso_section (a : Kˣ) (j i : Fin n) :
    DivisorLineSectionCompatible (ProjectiveLine.endpointReversal K)
      (normalizationIdeal_cartier K n hn p q h (a⁻¹) (reflectIndex j) (reflectIndex i))
      (normalizationIdeal_cartier K n hn p q h a j i)
      (reflectionNormalizationLineIso K n hn p q h a j i) := by
  let ht := normalizationIdeal_cartier K n hn p q h (a⁻¹) (reflectIndex j) (reflectIndex i)
  let hs := normalizationIdeal_cartier K n hn p q h a j i
  let w := reflection_normalization_ideal K n hn p q h a j i
  let _ := idealModulePullbackHom_isIso_of_cartier
    (ProjectiveLine.endpointReversal K) ht (w.symm ▸ hs)
  rw [reflectionNormalizationLineIso_def]
  exact divisorLinePullbackIsoOfEq_compatible _ _ _ _

/-- Restriction of the actual full-curve comparison is the canonical component comparison. -/
theorem reflectionLineIso_normalization (a : Kˣ) (j i : Fin n) :
    LinePullbackSquare (componentι K n i ≫ p).left (polygonReflection K hn p q h).left
      (ProjectiveLine.endpointReversal K) (componentι K n (reflectIndex i) ≫ p).left
      (reflection_normalization_left K n hn p q h i)
      (reflectionLineIso K n hn p q h a j) (normalizationLineIso K n hn p q h a j i)
      (normalizationLineIso K n hn p q h (a⁻¹) (reflectIndex j) (reflectIndex i))
      (reflectionNormalizationLineIso K n hn p q h a j i) :=
  divisorLineSectionCompatible_square _ _ _ _ _
    (reflectionLineIso_section K n hn p q h a j)
    (normalizationLineIso_section K n hn p q h a j i)
    (normalizationLineIso_section K n hn p q h (a⁻¹) (reflectIndex j) (reflectIndex i))
    (reflectionNormalizationLineIso_section K n hn p q h a j i)

/-- Every actual tensor power retains the full normalization square. -/
theorem reflectionLineIso_normalization_power
     (a : Kˣ) (j i : Fin n) (d : ℕ) :
    LinePullbackSquare (componentι K n i ≫ p).left (polygonReflection K hn p q h).left
      (ProjectiveLine.endpointReversal K) (componentι K n (reflectIndex i) ≫ p).left
      (reflection_normalization_left K n hn p q h i)
      (tensorPowerPullbackComparison _ (reflectionLineIso K n hn p q h a j) d)
      (tensorPowerPullbackComparison _ (normalizationLineIso K n hn p q h a j i) d)
      (tensorPowerPullbackComparison _
        (normalizationLineIso K n hn p q h (a⁻¹) (reflectIndex j) (reflectIndex i)) d)
      (tensorPowerPullbackComparison _
        (reflectionNormalizationLineIso K n hn p q h a j i) d) :=
  (reflectionLineIso_normalization K n hn p q h a j i).tensorPower d

end FLT.Mazur.PolygonMarkedSections
