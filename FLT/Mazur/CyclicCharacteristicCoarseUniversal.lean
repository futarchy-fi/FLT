/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicCoarseTransformation
public import FLT.Mazur.CyclicCharacteristicSheafChartMorphism

/-!
# Scheme-valued universality of the normalized coarse transformation

Every map from the actual normalized parameter sheaf to a represented fppf
sheaf factors uniquely through the constructed orbit scheme. Both existence
and uniqueness use the original full comparison arrows and chart equations.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {Y : Scheme}
  (d : unmarkedParameterSheaf n ⟶ Scheme.fppfTopology.uliftYoneda.{1}.obj Y)

/-- The actual chart morphisms recovered from a sheaf map assemble on the disjoint source. -/
def unmarkedSheafDisjointMorphism : normalizedDisjointSource n ⟶ Y :=
  Sigma.desc (unmarkedSheafChartMorphism n d)

/-- The assembled morphism respects the original full comparison arrows. -/
theorem unmarkedSheafDisjointMorphism_invariant :
    disjointComparisonSource n ≫ unmarkedSheafDisjointMorphism n d =
      disjointComparisonTarget n ≫ unmarkedSheafDisjointMorphism n d := by
  apply (disjointComparison_invariant_iff n _).mpr
  simpa only [unmarkedSheafDisjointMorphism, normalizedDisjointInclusion, Sigma.ι_comp_desc]
    using unmarkedSheafChartMorphism_invariant n d

/-- Descend a scheme-valued map from the parameter sheaf to the actual orbit scheme. -/
def normalizedCoarseDescend : invariantOrbitScheme n ⟶ Y :=
  invariantOrbitSchemeDescend n (unmarkedSheafDisjointMorphism n d)
    (unmarkedSheafDisjointMorphism_invariant n d)

/-- Coarse descent retains each original chart morphism. -/
@[reassoc] theorem normalizedCoarseDescend_chart (b : Bool) :
    normalizedCoarseChart n b ≫ normalizedCoarseDescend n d =
      unmarkedSheafChartMorphism n d b := by
  change (normalizedDisjointInclusion n b ≫ invariantOrbitSchemeProjection n) ≫
    invariantOrbitSchemeDescend n _ _ = _
  rw [Category.assoc, invariantOrbitSchemeDescend_fac]
  exact Sigma.ι_comp_desc _ _

/-- The factorization is an equality of actual sheaf morphisms. -/
theorem normalizedCoarseDescend_fac :
    normalizedCoarseTransformation n ≫
      Scheme.fppfTopology.uliftYoneda.map (normalizedCoarseDescend n d) = d := by
  apply unmarkedSheaf_hom_ext n
  ext T q
  obtain ⟨T⟩ := T
  obtain ⟨b, ⟨q⟩⟩ := q
  change ULift.up (((normalizedCoarseTransformation n).hom.app (Opposite.op T)
    ((unmarkedParameterSheafMap n).app (Opposite.op T) ⟨b, ULift.up q⟩)).down ≫
      normalizedCoarseDescend n d) = _
  rw [normalizedCoarseTransformation_evaluation]
  change ULift.up ((q ≫ normalizedCoarseChart n b) ≫
    normalizedCoarseDescend n d) = _
  rw [Category.assoc, normalizedCoarseDescend_chart]
  exact (unmarkedSheafChartMorphism_evaluation n d b q).symm

/-- Any sheaf factorization has the same actual chart morphisms. -/
theorem normalizedCoarse_factor_chart (g : invariantOrbitScheme n ⟶ Y)
    (hg : normalizedCoarseTransformation n ≫ Scheme.fppfTopology.uliftYoneda.map g = d)
    (b : Bool) : normalizedCoarseChart n b ≫ g = unmarkedSheafChartMorphism n d b := by
  have h := congrArg (fun k ↦ (k.hom.app (Opposite.op (normalizedLocus n b))
    ((unmarkedParameterSheafMap n).app (Opposite.op (normalizedLocus n b))
      ⟨b, ULift.up (𝟙 _)⟩)).down) hg
  change ((normalizedCoarseTransformation n).hom.app _ _).down ≫ g = _ at h
  rw [normalizedCoarseTransformation_evaluation] at h
  change (𝟙 _ ≫ normalizedCoarseChart n b) ≫ g = unmarkedSheafChartMorphism n d b at h
  simpa only [Category.id_comp] using h

/-- The scheme factor is unique, using the actual scheme coequalizer. -/
theorem normalizedCoarseDescend_unique (g : invariantOrbitScheme n ⟶ Y)
    (hg : normalizedCoarseTransformation n ≫ Scheme.fppfTopology.uliftYoneda.map g = d) :
    g = normalizedCoarseDescend n d := by
  apply invariantOrbitSchemeDescend_unique
  apply Sigma.hom_ext
  intro b
  change normalizedCoarseChart n b ≫ g =
    normalizedDisjointInclusion n b ≫ unmarkedSheafDisjointMorphism n d
  rw [show normalizedDisjointInclusion n b ≫ unmarkedSheafDisjointMorphism n d =
    unmarkedSheafChartMorphism n d b from Sigma.ι_comp_desc _ _]
  exact normalizedCoarse_factor_chart n d g hg b

/-- Universality holds for every scheme target and every morphism from the parameter sheaf. -/
theorem normalizedCoarse_universal :
    ∃! g : invariantOrbitScheme n ⟶ Y,
      normalizedCoarseTransformation n ≫ Scheme.fppfTopology.uliftYoneda.map g = d :=
  ⟨normalizedCoarseDescend n d, normalizedCoarseDescend_fac n d,
    fun g hg ↦ normalizedCoarseDescend_unique n d g hg⟩

end FLT.Mazur.CyclicCharacteristicOrbit
