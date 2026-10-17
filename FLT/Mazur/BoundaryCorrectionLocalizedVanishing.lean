/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BoundaryCorrectionCokernelBaseChange
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# Exact vanishing of localized boundary classes

The full correction cokernel comparison and module localization clear one
original denominator. This detects vanishing in the actual localized image,
without replacing that image by its possibly noninjective residual image.
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
  (β : D →ₗ[R] (∀ i, B i)) (U : Submonoid R)
  (S : Type*) [CommRing S] [Algebra R S] [IsLocalization U S]
set_option quotPrecheck false
local notation "g" => originalBoundaryCokernelMap φ p q v β
local notation "gS" => boundaryCokernelMap φ p q v β S

/-- A localized boundary class vanishes exactly when an original denominator kills its class. -/
theorem boundaryCokernelMap_localized_eq_zero_iff (t : D) :
    gS (1 ⊗ₜ[R] t) = 0 ↔ ∃ a : U, g (a.val • t) = 0 := by
  rw [← (boundaryCokernelBaseChangeEquiv φ p q v S).map_eq_zero_iff]
  change (1 ⊗ₜ[R] g t : S ⊗[R] _) = 0 ↔ _
  rw [show (1 ⊗ₜ[R] g t : S ⊗[R] _) = TensorProduct.mk R S _ 1 (g t) from rfl,
    IsLocalizedModule.eq_zero_iff U]
  simp only [Submonoid.smul_def, map_smul]

/-- Clearing a denominator produces simultaneous original boundary and mixed equations. -/
theorem boundaryCokernelMap_localized_eq_zero_iff_lift (t : D) :
    gS (1 ⊗ₜ[R] t) = 0 ↔
      ∃ (a : U) (w : ∀ i, A i), (∀ i, φ i (w i) = β (a.val • t) i) ∧
        ∀ i j, p i j (w i) = q i j (w j) := by
  rw [boundaryCokernelMap_localized_eq_zero_iff φ p q v β U S]
  simp only [originalBoundaryCokernelMap_eq_zero_iff]

end FLT.Mazur.BoundaryCorrectionIdeal
