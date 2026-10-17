/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionFlatImage

/-!
# The exact boundary kernel after flat scalar extension

Flat extension preserves every original relation among boundary parameters.
The kernel is the extension of the original kernel, and an exact original
restriction map remains exact at the extended boundary parameter module.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.BoundaryCorrectionIdeal
variable {R : Type*} [CommRing R] {ι : Type*} {A B : ι → Type*} {C : ι → ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)] [∀ i j, CommRing (C i j)]
  [∀ i, Algebra R (A i)] [∀ i, Algebra R (B i)] [∀ i j, Algebra R (C i j)]
  (φ : ∀ i, A i →ₐ[R] B i)
  (p : ∀ i j, A i →ₐ[R] C i j) (q : ∀ i j, A j →ₐ[R] C i j)
  (v : ∀ i, A i) {D : Type*} [AddCommGroup D] [Module R D]
  (β : D →ₗ[R] (∀ i, B i)) (S : Type*) [CommRing S] [Algebra R S] [Module.Flat R S]
set_option quotPrecheck false
local notation "g" => originalBoundaryCokernelMap φ p q v β
local notation "gS" => boundaryCokernelMap φ p q v β S

/-- Flat extension introduces no boundary relations beyond the extended original kernel. -/
theorem boundaryCokernelMap_ker_of_flat :
    LinearMap.ker gS = (LinearMap.ker g).baseChange S := by
  have h : Function.Exact ((LinearMap.ker g).subtype.baseChange S) ((g).baseChange S) :=
    Module.Flat.lTensor_exact S (LinearMap.exact_subtype_ker_map g)
  have he : LinearMap.ker ((g).baseChange S) = (LinearMap.ker g).baseChange S :=
    LinearMap.exact_iff.mp h
  rw [← he, ← boundaryCokernelBaseChangeEquiv_comp φ p q v S β]
  exact ((boundaryCokernelBaseChangeEquiv φ p q v S).ker_comp gS).symm

/-- Any exact original restriction map remains exact before the full extended obstruction. -/
theorem boundaryCokernelMap_exact_of_flat
    {U : Type*} [AddCommGroup U] [Module R U] (ρ : U →ₗ[R] D)
    (hρ : LinearMap.ker g = LinearMap.range ρ) :
    Function.Exact (ρ.baseChange S) gS := by
  rw [LinearMap.exact_iff, boundaryCokernelMap_ker_of_flat, hρ,
    CompatibleErrorBaseChange.range_baseChange]

/-- A zero extended boundary obstruction belongs to the extended restriction image. -/
theorem boundaryCokernelMap_eq_zero_iff_of_flat
    {U : Type*} [AddCommGroup U] [Module R U] (ρ : U →ₗ[R] D)
    (hρ : LinearMap.ker g = LinearMap.range ρ) (x : S ⊗[R] D) :
    gS x = 0 ↔ ∃ y : S ⊗[R] U, ρ.baseChange S y = x :=
  boundaryCokernelMap_exact_of_flat φ p q v β S ρ hρ x

end FLT.Mazur.BoundaryCorrectionIdeal
