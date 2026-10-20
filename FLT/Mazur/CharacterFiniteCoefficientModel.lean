/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterAlgebraScalarExtension
public import Mathlib.RingTheory.FiniteType

/-!
# Finite coefficient models retaining the original characters

A finite list of elements of a finite character algebra is defined over a
finite-type integer subalgebra of its actual coefficient ring. The character
basis is unchanged, and coefficient inclusion is injective.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.CharacterFiniteCoefficientModel

variable {R G ι : Type*} [CommRing R] (v : ι → AddMonoidAlgebra R G) (s : Set R)

/-- Adjoin the actual coefficients, together with any prescribed base elements. -/
def coefficientRing : Subalgebra ℤ R :=
  Algebra.adjoin ℤ (s ∪ Set.range (fun p : ι × G => (v p.1).coeff p.2))

/-- Only finitely many integer coefficients are required. -/
theorem coefficientRing_finiteType [Finite G] [Finite ι] (hs : s.Finite) :
    Algebra.FiniteType ℤ (coefficientRing v s) :=
  Algebra.FiniteType.adjoin_of_finite (hs.union (Set.finite_range _))

/-- Every prescribed base element is retained. -/
theorem subset_coefficientRing : s ⊆ coefficientRing v s :=
  fun _ h => Algebra.subset_adjoin (Or.inl h)

/-- Every original character coefficient is retained. -/
theorem coeff_mem (i : ι) (g : G) : (v i).coeff g ∈ coefficientRing v s :=
  Algebra.subset_adjoin (Or.inr ⟨(i, g), rfl⟩)

variable [AddCommMonoid G]

/-- Inclusion changes coefficients only, leaving all characters in place. -/
def inclusion : AddMonoidAlgebra (coefficientRing v s) G →+* AddMonoidAlgebra R G :=
  AddMonoidAlgebra.mapRingHom G (coefficientRing v s).val.toRingHom

/-- The actual coefficient inclusion loses no character-algebra elements. -/
theorem inclusion_injective : Function.Injective (inclusion v s) :=
  AddMonoidAlgebra.map_injective _ Subtype.val_injective

/-- Each original element has a representative on the same character basis. -/
theorem exists_lift (i : ι) : ∃ x, inclusion v s x = v i := by
  change v i ∈ Set.range (AddMonoidAlgebra.map (coefficientRing v s).val.toAddMonoidHom)
  rw [AddMonoidAlgebra.range_map]
  exact fun g => ⟨⟨(v i).coeff g, coeff_mem v s i g⟩, rfl⟩

/-- The original element over the finite coefficient ring. -/
def lift (i : ι) : AddMonoidAlgebra (coefficientRing v s) G :=
  (exists_lift v s i).choose

/-- Recovery is equality of the full elements, including all coefficients. -/
@[simp] theorem inclusion_lift (i : ι) : inclusion v s (lift v s i) = v i :=
  (exists_lift v s i).choose_spec

/-- Every coefficient of the lift is exactly its original coefficient. -/
theorem lift_coeff (i : ι) (g : G) : ((lift v s i).coeff g : R) = (v i).coeff g := by
  have h := congrArg (fun x : AddMonoidAlgebra R G => x.coeff g) (inclusion_lift v s i)
  exact h

end FLT.Mazur.CharacterFiniteCoefficientModel
