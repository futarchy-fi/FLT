/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RepresentationTheory.Basic
public import Mathlib.LinearAlgebra.Span.Basic

/-! # The actual unit-valued character of a scalar representation -/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions
variable {k G : Type*} [Field k] [Group G] (δ : Representation k G k)

/-- Evaluation at one turns a scalar representation into its unit-valued character. -/
def scalarRepresentationCharacter : G →* kˣ :=
  (show G →* k from
    { toFun := fun g ↦ δ g 1
      map_one' := by rw [map_one δ]; rfl
      map_mul' := fun g h ↦ by
        change δ (g * h) 1 = δ g 1 * δ h 1
        rw [map_mul]
        change δ g (δ h 1) = _
        calc
          δ g (δ h 1) = δ h 1 • δ g 1 := by
            conv_lhs => rw [← mul_one (δ h 1), ← smul_eq_mul, LinearMap.map_smul]
          _ = δ g 1 * δ h 1 := mul_comm _ _ }).toHomUnits

/-- The scalar character acts on every vector by the original scalar representation. -/
theorem scalarRepresentationCharacter_apply (g : G) (x : k) :
    δ g x = (scalarRepresentationCharacter δ g : k) * x := by
  change δ g x = δ g 1 * x
  conv_lhs => rw [← mul_one x, ← smul_eq_mul, LinearMap.map_smul]
  exact mul_comm _ _

/-- A square-one scalar representation gives a quadratic unit character. -/
theorem scalarRepresentationCharacter_sq (hδ : ∀ g, δ g * δ g = 1) (g : G) :
    scalarRepresentationCharacter δ g ^ 2 = 1 := by
  apply Units.ext
  have h := congrArg (fun f : Module.End k k ↦ f 1) (hδ g)
  change δ g (δ g 1) = 1 at h
  rw [scalarRepresentationCharacter_apply, scalarRepresentationCharacter_apply, mul_one] at h
  simpa [pow_two] using h

end GaloisRepresentation.Extensions
