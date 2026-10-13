/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertRefinedSchemeNeighborhood
public import FLT.Mazur.VariableHilbertDescendedGeometry

/-!
# Fppf geometry of the entire original source restriction

The constructed projection from the whole original restriction to a refined
model is an actual fppf cover. Etale translation bases give an etale cover,
with the full original restricted relation as its effective scheme kernel pair.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertBaseOpenChart
open HilbertChart CartierAbel SchemePicard FCurve VariableHilbertFppfRefinement
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left]
  {Z : Over (Spec (.of R))} (π : variableHilbertTest f d W ⟶ Z)
  (H : IsPullback
    (variableChartRelationFst f hL d W ((relativeFppfSheaf f).obj.map b.op c))
    (variableChartRelationSnd f hL d W ((relativeFppfSheaf f).obj.map b.op c)) π π)
  [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left]
local notation "F" => refinedModelFullProjection f hL d b c π H

omit [LocallyOfFinitePresentation π.left] [Surjective π.left] in
/-- The entire original source maps flatly to the model. -/
theorem refinedModelFullProjection_flat : Flat (F).left := by
  dsimp only [refinedModelFullProjection, Over.comp_left]
  infer_instance

omit [Flat π.left] [LocallyOfFinitePresentation π.left] in
/-- Every point of the model lifts to the entire original restriction. -/
theorem refinedModelFullProjection_surjective : Surjective (F).left := by
  dsimp only [refinedModelFullProjection, Over.comp_left]
  infer_instance

/-- Finite presentation holds for the whole original source, not just refined parameters. -/
theorem refinedModelFullProjection_locallyOfFinitePresentation
    [LocallyOfFinitePresentation V.hom] : LocallyOfFinitePresentation (F).left := by
  let _ := descendedProjection_locallyOfFinitePresentation f hL d b c π H
  dsimp only [refinedModelFullProjection, Over.comp_left]
  infer_instance

/-- Smooth original translations give a smooth full original projection. -/
theorem refinedModelFullProjection_smooth [Smooth V.hom] : Smooth (F).left := by
  let _ := descendedProjection_smooth f hL d b c π H
  dsimp only [refinedModelFullProjection, Over.comp_left]
  infer_instance

/-- Etale original translations give an etale full original projection. -/
theorem refinedModelFullProjection_etale [Etale V.hom] : Etale (F).left := by
  let _ := descendedProjection_etale f hL d b c π H
  dsimp only [refinedModelFullProjection, Over.comp_left]
  infer_instance

/-- The full original scheme restriction supplies an actual fppf cover of the model. -/
theorem refinedModelFullProjection_fppf [LocallyOfFinitePresentation V.hom] :
    Presieve.singleton (F).left ∈ Scheme.fppfPrecoverage Z.left := by
  let _ := refinedModelFullProjection_flat f hL d b c π H
  let _ := refinedModelFullProjection_surjective f hL d b c π H
  let _ := refinedModelFullProjection_locallyOfFinitePresentation f hL d b c π H
  exact Scheme.Hom.singleton_mem_fppfPrecoverage _

/-- The full original restricted relation has the constructed scheme model as coequalizer. -/
def refinedModelFullCoforkIsColimit [LocallyOfFinitePresentation V.hom] :
    IsColimit (Cofork.ofπ (F).left
      (congrArg Over.Hom.left (refinedModelFullProjection_condition f hL d b c π H))) := by
  let _ := refinedModelFullProjection_flat f hL d b c π H
  let _ := refinedModelFullProjection_surjective f hL d b c π H
  let _ := refinedModelFullProjection_locallyOfFinitePresentation f hL d b c π H
  exact isColimitCoforkOfEffectiveEpi (F).left _
    ((refinedModelFullProjection_isPullback f hL d b c π H).map (Over.forget _)).isLimit

end FLT.Mazur.OrderedHilbertBaseOpenChart
