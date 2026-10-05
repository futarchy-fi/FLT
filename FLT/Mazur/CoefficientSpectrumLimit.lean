/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientStageColimit
public import Mathlib.AlgebraicGeometry.AffineTransitionLimit

/-!
# The coefficient inverse system of affine bases

The spectra of the finite coefficient enlargements form a cofiltered diagram
with affine transition maps. Its canonical cone has vertex `Spec A` and is a
limit cone. This supplies the base system for approximation of scheme models;
it does not assert descent of properness.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {A : Type u} [CommRing A] (S₀ : Subalgebra ℤ A)

/-- Spectra of the finite coefficient rings, with arrows toward smaller stages. -/
def coefficientSpectrumDiagram : (CoefficientStage S₀)ᵒᵖ ⥤ Scheme.{u} :=
  (coefficientStageDiagram S₀).op ⋙ Scheme.Spec

/-- The cone of the original affine base over its coefficient spectra. -/
def coefficientSpectrumCone : Cone (coefficientSpectrumDiagram S₀) :=
  Scheme.Spec.mapCone (coefficientStageCocone S₀).op

instance (i j : (CoefficientStage S₀)ᵒᵖ) (f : i ⟶ j) :
    IsAffineHom ((coefficientSpectrumDiagram S₀).map f) := by
  dsimp [coefficientSpectrumDiagram, coefficientStageDiagram]
  infer_instance

/-- The canonical affine-base cone is a limit. -/
def coefficientSpectrumIsLimit [Algebra.FiniteType ℤ S₀] :
    IsLimit (coefficientSpectrumCone S₀) :=
  isLimitOfPreserves Scheme.Spec (coefficientStageIsColimit S₀).op

/-- The limit projections are precisely the coefficient-inclusion spectrum maps. -/
theorem coefficientSpectrumCone_π (S : CoefficientStage S₀) :
    (coefficientSpectrumCone S₀).π.app (.op S) =
      Spec.map (CommRingCat.ofHom S.val.val.toRingHom) := rfl

end FLT.Mazur.Approximation
