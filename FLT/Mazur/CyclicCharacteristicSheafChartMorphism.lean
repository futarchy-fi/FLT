/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicUnmarkedSchemeDescent

/-!
# Recovering actual chart morphisms from a scheme-valued sheaf map

Evaluation on the identity parameters recovers the two chart morphisms.
Naturality supplies every parameter equation, and the original quotient
forces full unmarked invariance without an additional hypothesis.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {Y : Scheme}
  (d : unmarkedParameterSheaf n ⟶ Scheme.fppfTopology.uliftYoneda.{1}.obj Y)

/-- Recover a chart morphism by evaluating the given sheaf map on the identity parameter. -/
def unmarkedSheafChartMorphism (b : Bool) : normalizedLocus n b ⟶ Y :=
  ((unmarkedParameterSheafMap n ≫ d.hom).app (Opposite.op (normalizedLocus n b))
    ⟨b, ULift.up (𝟙 _)⟩).down

/-- Naturality recovers the prescribed value on every original parameter. -/
theorem unmarkedSheafChartMorphism_evaluation {T : Scheme} (b : Bool)
    (q : T ⟶ normalizedLocus n b) :
    (unmarkedParameterSheafMap n ≫ d.hom).app (Opposite.op T) ⟨b, ULift.up q⟩ =
      ULift.up (q ≫ unmarkedSheafChartMorphism n d b) := by
  have h := (unmarkedParameterSheafMap n ≫ d.hom).naturality_apply q.op
    ⟨b, ULift.up (𝟙 _)⟩
  change (unmarkedParameterSheafMap n ≫ d.hom).app (Opposite.op T)
    ⟨b, ULift.up (q ≫ 𝟙 _)⟩ = ULift.up (q ≫ unmarkedSheafChartMorphism n d b) at h
  simpa only [Category.comp_id] using h

/-- Every scheme-valued sheaf morphism comes from its recovered chart morphisms. -/
theorem unmarkedSheafChartMorphism_parameters :
    unmarkedParameterSheafMap n ≫ d.hom =
      schemeParameterMap n (unmarkedSheafChartMorphism n d) := by
  ext T q
  exact unmarkedSheafChartMorphism_evaluation n d q.1 q.2.down

/-- The recovered chart morphisms automatically respect the full comparison relation. -/
theorem unmarkedSheafChartMorphism_invariant :
    UnmarkedInvariant n (unmarkedSheafChartMorphism n d) :=
  unmarkedInvariant_of_sheaf_factor n _ d (unmarkedSheafChartMorphism_parameters n d)

/-- Recovering chart morphisms and descending again retains the original sheaf map. -/
theorem unmarkedSheafChartMorphism_desc :
    unmarkedSchemeDesc n (unmarkedSheafChartMorphism n d)
      (unmarkedSheafChartMorphism_invariant n d) = d := by
  apply unmarkedSheaf_hom_ext n
  exact (unmarkedParameterSheafMap_desc n _ _).trans
    (unmarkedSheafChartMorphism_parameters n d).symm

/-- Two scheme-valued sheaf morphisms agree when their actual chart morphisms agree. -/
theorem unmarkedSheafChartMorphism_ext
    {a b : unmarkedParameterSheaf n ⟶ Scheme.fppfTopology.uliftYoneda.{1}.obj Y}
    (h : ∀ c, unmarkedSheafChartMorphism n a c = unmarkedSheafChartMorphism n b c) :
    a = b := by
  apply unmarkedSheaf_hom_ext n
  rw [unmarkedSheafChartMorphism_parameters, unmarkedSheafChartMorphism_parameters]
  exact congrArg (schemeParameterMap n) (funext h)

end FLT.Mazur.CyclicCharacteristicAtlas
