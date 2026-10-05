/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CoefficientStageDiagram
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.CategoryTheory.Limits.Types.Filtered

/-!
# The original ring is the colimit of its coefficient stages

Every element occurs at a finite coefficient stage, and equality is detected
by the literal inclusions. The resulting universal property is in
`CommRingCat`, so it can be transported to an inverse limit of spectra.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.Approximation

universe u

variable {A : Type u} [CommRing A] (S₀ : Subalgebra ℤ A)
  [Algebra.FiniteType ℤ S₀]

/-- The underlying sets of the coefficient stages have colimit `A`. -/
def coefficientStageTypesIsColimit :
    IsColimit ((forget CommRingCat).mapCocone (coefficientStageCocone S₀)) := by
  apply Types.FilteredColimit.isColimitOf'
  · intro a
    obtain ⟨S, ha⟩ := exists_coefficientStage_mem S₀ a
    exact ⟨S, ⟨a, ha⟩, rfl⟩
  · intro S x y h
    exact ⟨S, 𝟙 S, congrArg (fun z ↦ z) (Subtype.ext h)⟩

/-- The coefficient inclusions present the original commutative ring as a colimit. -/
def coefficientStageIsColimit : IsColimit (coefficientStageCocone S₀) := by
  letI := reflectsColimit_of_reflectsIsomorphisms
    (coefficientStageDiagram S₀) (forget CommRingCat)
  exact isColimitOfReflects (forget CommRingCat) (coefficientStageTypesIsColimit S₀)

end FLT.Mazur.Approximation
