/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarImageSourceGenerators
public import FLT.Mazur.LocalizedImageFiniteWitness
public import Mathlib.RingTheory.Flat.Localization

/-!
# Finite original lifts from vanishing of a localized image

A finite original family generating the localized source modulo restrictions
needs just one original denominator and finitely many exact original lifts.
This uses the entire connecting kernel, so the lifts satisfy every equation.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalizedImageFiniteLifts
variable {R U D M : Type*} [CommRing R]
  [AddCommGroup U] [Module R U] [AddCommGroup D] [Module R D]
  [AddCommGroup M] [Module R M]
  (ρ : U →ₗ[R] D) (g : D →ₗ[R] M)
  (hker : LinearMap.ker g = LinearMap.range ρ)

include hker in
/-- An original annihilator of a connecting value constructs an exact scaled restriction lift. -/
theorem smul_eq_zero_iff_lift (a : R) (t : D) :
    a • g t = 0 ↔ ∃ v : U, ρ v = a • t := by
  rw [← map_smul]
  change a • t ∈ LinearMap.ker g ↔ _
  rw [hker]
  rfl

variable (V : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization V S]

include hker in
/-- A finite relative source frame gives a common-denominator test for full local vanishing. -/
theorem eq_zero_iff_finite_lifts {n : ℕ} (t : Fin n → D)
    (hspan : Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[R] t j : S ⊗[R] D))) ⊔
      LinearMap.range (ρ.baseChange S) = ⊤) :
    g.baseChange S = 0 ↔ ∃ (a : V) (v : Fin n → U), ∀ j, ρ (v j) = a.val • t j := by
  let _ : Module.Flat R S := IsLocalization.flat S V
  have ht := (ScalarImageSourceGenerators.original_span_iff ρ g hker S t).mpr hspan
  rw [LocalizedImageFiniteWitness.baseChange_eq_zero_iff_common_annihilator V S g t ht]
  constructor
  · rintro ⟨a, ha⟩
    have hv := fun j ↦ (smul_eq_zero_iff_lift ρ g hker a.val (t j)).mp (ha j)
    choose v hv using hv
    exact ⟨a, v, hv⟩
  · rintro ⟨a, v, hv⟩
    exact ⟨a, fun j ↦ (smul_eq_zero_iff_lift ρ g hker a.val (t j)).mpr ⟨v j, hv j⟩⟩

include hker in
/-- A finite local image constructs a finite original source frame and its exact lift test. -/
theorem exists_finite_lift_test (hfg : (LinearMap.range (g.baseChange S)).FG) :
    ∃ (n : ℕ) (t : Fin n → D),
      (Submodule.span S (Set.range (fun j ↦ (1 ⊗ₜ[R] t j : S ⊗[R] D))) ⊔
        LinearMap.range (ρ.baseChange S) = ⊤) ∧
      (g.baseChange S = 0 ↔ ∃ (a : V) (v : Fin n → U), ∀ j, ρ (v j) = a.val • t j) := by
  let _ : Module.Flat R S := IsLocalization.flat S V
  obtain ⟨n, t, ht⟩ :=
    (ScalarImageSourceGenerators.fg_iff_original_source_generators ρ g hker S).mp hfg
  exact ⟨n, t, ht, eq_zero_iff_finite_lifts ρ g hker V S t ht⟩

end FLT.Mazur.LocalizedImageFiniteLifts
