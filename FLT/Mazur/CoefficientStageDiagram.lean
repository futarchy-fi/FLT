/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CommonCoefficientStage
public import Mathlib.Algebra.Category.Ring.FilteredColimits

/-!
# The filtered diagram of finite coefficient enlargements

Above any finite-type integer subalgebra, the finite-type coefficient stages
form a filtered poset. Their inclusions define a diagram of commutative rings
with a canonical cocone to the original ring.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

namespace FLT.Mazur.Approximation

universe u

variable {A : Type u} [CommRing A] (S₀ : Subalgebra ℤ A)

/-- Finite-type coefficient stages containing the chosen initial stage. -/
abbrev CoefficientStage :=
  {S : Subalgebra ℤ A // S₀ ≤ S ∧ Algebra.FiniteType ℤ S}

instance : PartialOrder (CoefficientStage S₀) :=
  inferInstanceAs (PartialOrder {S : Subalgebra ℤ A //
    S₀ ≤ S ∧ Algebra.FiniteType ℤ S})

instance (S : CoefficientStage S₀) : Algebra.FiniteType ℤ S.val := S.property.2

instance [Algebra.FiniteType ℤ S₀] : Nonempty (CoefficientStage S₀) :=
  ⟨⟨S₀, le_rfl, inferInstance⟩⟩

instance [Algebra.FiniteType ℤ S₀] : IsDirectedOrder (CoefficientStage S₀) where
  directed S T := by
    let R : Bool → Subalgebra ℤ A := fun b ↦ if b then S.val else T.val
    have hR : ∀ b, Algebra.FiniteType ℤ (R b) := by
      intro b
      cases b <;> dsimp [R] <;> infer_instance
    obtain ⟨U, hU, _, h₀U, hRU⟩ :=
      exists_common_coefficient_extension S₀ R hR ∅ Set.finite_empty
    exact ⟨⟨U, h₀U, hU⟩, hRU true, hRU false⟩

/-- Every coefficient belongs to an enlargement of the initial stage. -/
theorem exists_coefficientStage_mem [Algebra.FiniteType ℤ S₀] (a : A) :
    ∃ S : CoefficientStage S₀, a ∈ S.val := by
  obtain ⟨S, hS, ha, h₀S, _⟩ := exists_common_coefficient_extension S₀
    (fun _ : Empty ↦ S₀) (fun _ ↦ inferInstance) {a} (Set.finite_singleton a)
  exact ⟨⟨S, h₀S, hS⟩, ha (Set.mem_singleton a)⟩

/-- The coefficient rings and their literal inclusion homomorphisms. -/
def coefficientStageDiagram : CoefficientStage S₀ ⥤ CommRingCat.{u} where
  obj S := .of S.val
  map f := CommRingCat.ofHom (Subalgebra.inclusion (leOfHom f)).toRingHom
  map_id _ := by ext; rfl
  map_comp _ _ := by ext; rfl

/-- Inclusion of every coefficient ring into the original ring. -/
def coefficientStageCocone : Cocone (coefficientStageDiagram S₀) where
  pt := .of A
  ι.app S := CommRingCat.ofHom S.val.val.toRingHom
  ι.naturality _ _ _ := by ext; rfl

end FLT.Mazur.Approximation
