/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientModelHomDescent

/-!
# Recovery projections from a specified original scheme

A Cartesian identification of an original scheme with the recovered model
supplies its actual projections to every enlarged coefficient model.
The projections retain both the original model map and the base map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {A : Type u} [CommRing A] (S₀ : Subalgebra ℤ A)
  {X Y : Scheme.{u}} (p : Y ⟶ Spec (.of S₀))
  (e : X ≅ (coefficientModelCone S₀ p).pt) (i : (CoefficientStage S₀)ᵒᵖ)

/-- The specified original scheme's actual projection to a coefficient enlargement. -/
def coefficientActualRecovery : X ⟶ (coefficientModelDiagram S₀ p).obj i :=
  e.hom ≫ (coefficientModelCone S₀ p).π.app i

/-- Enlargement preserves the original projection to the initial model. -/
@[reassoc] theorem coefficientActualRecovery_fst :
    coefficientActualRecovery S₀ p e i ≫ (coefficientModelToInitial S₀ p).app i =
      e.hom ≫ pullback.fst p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)) := by
  rw [coefficientActualRecovery, Category.assoc, coefficientModelCone_toInitial]

/-- Enlargement preserves the original projection to the complete coefficient base. -/
@[reassoc] theorem coefficientActualRecovery_snd :
    coefficientActualRecovery S₀ p e i ≫
      pullback.snd p ((coefficientSpectrumToInitial S₀).app i) =
        (e.hom ≫ pullback.snd p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom))) ≫
          (coefficientSpectrumCone S₀).π.app i := by
  rw [coefficientActualRecovery, Category.assoc, (coefficientModelCone_isPullback S₀ p i).w]
  exact (Category.assoc _ _ _).symm

/-- The specified original scheme is the Cartesian recovery at every coefficient enlargement. -/
theorem coefficientActualRecovery_isPullback :
    IsPullback (coefficientActualRecovery S₀ p e i)
      (e.hom ≫ pullback.snd p (Spec.map (CommRingCat.ofHom S₀.val.toRingHom)))
      (pullback.snd p ((coefficientSpectrumToInitial S₀).app i))
      ((coefficientSpectrumCone S₀).π.app i) := by
  apply (coefficientModelCone_isPullback S₀ p i).of_iso e.symm
    (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · simp [coefficientActualRecovery]
  · simp
  · simp
  · simp

end FLT.Mazur.Approximation
