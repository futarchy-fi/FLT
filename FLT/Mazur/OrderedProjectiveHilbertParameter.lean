/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveAmbientHilbertParameter
public import FLT.Mazur.OrderedRelativeIdealBaseChange

/-!
# Ordered divisors map to the full Hilbert scheme

Classify the actual ordered graph family. Universal pullback recovers its
entire ideal, and equality of full families proves permutation invariance
of the classifying morphism, including all diagonals and degree zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.HilbertChart

namespace FLT.Mazur.OrderedCurvePower

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {Z : Scheme} (z : Z ⟶ Spec (.of R))
variable [SmoothOfRelativeDimension 1 z] [IsProper z]
variable {B : Type} [CommRing B] {ι : Type}
variable (e : Z ⟶ ProjectiveSpace.space B ι) [IsClosedImmersion e] (d : ℕ)
variable {X : Scheme} (s : X ⟶ Spec (.of R))
variable (x : Fin d → (X ⟶ Z)) (hx : ∀ i, x i ≫ z = s)

/-- Classify the full divisor family of any ordered tuple. -/
def tupleHilbertParameter : (allAffineAmbientCharts z).GluedParameters d s :=
  projectiveAmbientParameter z e d s (tupleRelativeIdealFamily z d s x hx)

/-- Its universal pullback is the entire original ordered divisor family. -/
theorem tupleHilbertParameter_family :
    (allAffineAmbientCharts z).parameterFamily d s (tupleHilbertParameter z e d s x hx) =
      tupleRelativeIdealFamily z d s x hx :=
  projectiveAmbientParameter_family z e d s _

/-- Full-family uniqueness identifies all permutations of a tuple. -/
theorem tupleHilbertParameter_permutation (σ : Equiv.Perm (Fin d)) :
    tupleHilbertParameter z e d s (fun i ↦ x (σ i)) (fun i ↦ hx (σ i)) =
      tupleHilbertParameter z e d s x hx := by
  apply (allAffineAmbientCharts z).parameterFamily_injective d s
  rw [tupleHilbertParameter_family, tupleHilbertParameter_family,
    tupleRelativeIdealFamily_permutation]

/-- The actual ordered parameter space maps to the full Hilbert representative. -/
def orderedHilbertParameter : (allAffineAmbientCharts z).GluedParameters d (base z d) :=
  tupleHilbertParameter z e d (base z d) (point z d) (point_base z d)

/-- Pulling back the universal Hilbert ideal recovers the original ordered graph product. -/
theorem orderedHilbertParameter_ideal :
    ((allAffineAmbientCharts z).parameterFamily d (base z d)
      (orderedHilbertParameter z e d)).val =
        (divisorIdeal z d).comap (pullbackSymmetry (base z d) z).hom := by
  rw [orderedHilbertParameter, tupleHilbertParameter_family]
  rfl

end FLT.Mazur.OrderedCurvePower
