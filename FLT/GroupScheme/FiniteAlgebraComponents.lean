/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.HenselianConnectedLocal
public import Mathlib.RingTheory.TensorProduct.Finite

/-! # Local factors of finite algebras over a field -/

@[expose] public noncomputable section

namespace FiniteAlgebra

variable (A : Type*) [CommRing A] [IsArtinianRing A]

/-- Indices for the Artinian local factors. -/
abbrev ComponentIndex := MaximalSpectrum (A ⧸ (⊥ : Ideal A))

/-- The primitive idempotent of a local factor. -/
def componentIdempotent (m : ComponentIndex A) : A :=
  ThreeAdicPlan.componentIdempotent (⊥ : Ideal A) m

/-- The local factor as a quotient of the original algebra. -/
abbrev Component (m : ComponentIndex A) := A ⧸ Ideal.span {1 - componentIdempotent A m}

/-- The component elements are idempotent. -/
theorem componentIdempotent_isIdempotent (m : ComponentIndex A) :
    IsIdempotentElem (componentIdempotent A m) :=
  ThreeAdicPlan.componentIdempotent_isIdempotent _ m

/-- Every component is connected. -/
theorem component_idempotent_trivial (m : ComponentIndex A) (d : Component A m)
    (hd : IsIdempotentElem d) : d = 0 ∨ d = 1 :=
  ThreeAdicPlan.componentFactor_idempotent_trivial _ m d hd

variable (k : Type*) [Field k] [Algebra k A] [Module.Finite k A]

instance component_finite (m : ComponentIndex A) : Module.Finite k (Component A m) :=
  Module.Finite.of_surjective (Ideal.Quotient.mkₐ k _).toLinearMap Ideal.Quotient.mk_surjective

/-- The factors are nonzero. -/
instance component_nontrivial (m : ComponentIndex A) : Nontrivial (Component A m) := by
  let : Field ((A ⧸ (⊥ : Ideal A)) ⧸ m.asIdeal) := Ideal.Quotient.field m.asIdeal
  apply Ideal.Quotient.nontrivial_iff.mpr
  intro h
  have he0 : componentIdempotent A m = 0 := by
    obtain ⟨a, ha⟩ := Ideal.mem_span_singleton.mp
      (h ▸ (show componentIdempotent A m ∈ (⊤ : Ideal A) from trivial))
    have hh := congrArg (componentIdempotent A m * ·) ha
    rw [← mul_assoc, (componentIdempotent_isIdempotent A m).mul_one_sub_self,
      zero_mul, (componentIdempotent_isIdempotent A m).eq] at hh
    exact hh
  have hh := congrArg (fun x ↦ ThreeAdicPlan.componentResidueMap (⊥ : Ideal A) x m) he0
  simp [componentIdempotent] at hh

/-- A finite connected factor is a local ring. -/
instance component_isLocalRing (m : ComponentIndex A) : IsLocalRing (Component A m) := by
  exact ThreeAdicPlan.isLocalRing_of_henselian_idempotent_trivial (⊥ : Ideal (Component A m))
    (component_idempotent_trivial A m)

/-- The original algebra is the product of its local quotient factors. -/
def componentEquiv : A ≃ₐ[k] Π m : ComponentIndex A, Component A m :=
  ThreeAdicPlan.primitiveComponentEquiv (⊥ : Ideal A)

end FiniteAlgebra
