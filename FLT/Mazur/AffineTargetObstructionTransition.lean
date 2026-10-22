/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineObstructionBaseChange
public import FLT.Mazur.FlatTargetObstructionMap

/-!
# The actual affine obstruction transition after target extension

The old algebra maps into the extended target through the scalar-extension
algebra. Its ideal tensor transition is the composite of the scalar-extension
transition with the actual target comparison, including for localizations.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.AffineTargetObstructionTransition
variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (S T : Type*) [CommRing S] [Algebra R S] [CommRing T] [Algebra S T]
  [Algebra (S ⊗[R] A) T] [IsScalarTower S (S ⊗[R] A) T]

/-- The actual original algebra map into the extended target. -/
def rightMap : A →+* T :=
  (algebraMap (S ⊗[R] A) T).comp (AffineObstructionBaseChange.rightMap S)

/-- This target extension retains the original commutative base-change square. -/
theorem square : (rightMap (R := R) (A := A) S T).comp (algebraMap R A) =
    (algebraMap S T).comp (algebraMap R S) := by
  rw [rightMap, RingHom.comp_assoc, AffineObstructionBaseChange.square,
    ← RingHom.comp_assoc, ← IsScalarTower.algebraMap_eq S (S ⊗[R] A) T]

/-- The actual transition equals the composite comparison on every old ideal tensor. -/
theorem transition_eq (I : Ideal R) (z : A ⊗[R] I) :
    IdealTensorKernel.transition (algebraMap R S) (rightMap (R := R) S T) (square S T) I z =
      FlatTargetObstructionMap.comparison T (I.map (algebraMap R S))
        (IdealTensorKernel.transition (algebraMap R S)
          (AffineObstructionBaseChange.rightMap S) (AffineObstructionBaseChange.square S) I z) := by
  induction z with
  | tmul a i =>
    simp only [IdealTensorKernel.transition_tmul, FlatTargetObstructionMap.comparison_tmul]
    rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end FLT.Mazur.AffineTargetObstructionTransition
