/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelFaithfulRepresentation
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Closed faithfulness extends over an entire local base

The faithful marking locus is open. A parameter over a local spectrum whose
closed image lies in that locus factors through it on the whole base.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : Over S) [GrpObj E] [IsSeparated E.hom]
  (A : Type) [Group A] [Fintype A] {R : Type} [CommRing R] [IsLocalRing R]
  {g : Spec (.of R) ⟶ S} (f : Over.mk g ⟶ homScheme E A)
  (hf : f.left (IsLocalRing.closedPoint R) ∈ faithfulOpen E A)

include hf in
/-- The closed faithful image forces every image point into the original faithful open. -/
theorem localFaithful_range : Set.range f.left ⊆ faithfulOpen E A := by
  rintro _ ⟨x, rfl⟩
  exact ((IsLocalRing.specializes_closedPoint x).map f.left.continuous).mem_open
    (faithfulOpen E A).isOpen hf

/-- The actual marking parameter factors through the faithful open over the entire local base. -/
def localFaithfulLift : Over.mk g ⟶ faithfulScheme E A := by
  refine Over.homMk (IsOpenImmersion.lift (faithfulOpen E A).ι f.left ?_) ?_
  · rintro _ ⟨x, rfl⟩
    exact ⟨⟨f.left x, localFaithful_range E A f hf ⟨x, rfl⟩⟩, rfl⟩
  · change _ ≫ (faithfulOpen E A).ι ≫ (homScheme E A).hom = g
    rw [IsOpenImmersion.lift_fac_assoc, f.w]
    rfl

/-- Factorization retains the whole original parameter map and thus all marked sections. -/
@[reassoc] theorem localFaithfulLift_inclusion :
    localFaithfulLift E A f hf ≫ faithfulInclusion E A = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac (faithfulOpen E A).ι f.left _

end FLT.Mazur.AuxiliaryLevel
