/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarImageOriginalGenerators
public import Mathlib.RingTheory.Localization.BaseChange

/-!
# One original denominator for finite generators of a local image

Only the selected original values are asserted to have a common annihilator.
Their local spanning property then detects vanishing of the full localized
map, without asserting global finite generation or a global annihilator.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.LocalizedImageFiniteWitness
variable {R D M : Type*} [CommRing R]
  [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M]
  (U : Submonoid R) (S : Type*) [CommRing S] [Algebra R S] [IsLocalization U S]

/-- A finite family vanishing on localization admits one original denominator. -/
theorem exists_common_annihilator {ι : Type*} [Finite ι] (x : ι → M)
    (hx : ∀ i, (1 ⊗ₜ[R] x i : S ⊗[R] M) = 0) :
    ∃ a : U, ∀ i, a.val • x i = 0 := by
  classical
  let _ := Fintype.ofFinite ι
  have hi : ∀ i, ∃ a : U, a.val • x i = 0 := by
    intro i
    exact (IsLocalizedModule.eq_zero_iff U (TensorProduct.mk R S M 1) (m := x i)).mp (hx i)
  have hs : ∀ s : Finset ι, ∃ a : U, ∀ i ∈ s, a.val • x i = 0 := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp only [Finset.notMem_empty, false_implies, implies_true]⟩
    | @insert i s _ ih =>
      obtain ⟨a, ha⟩ := ih
      obtain ⟨b, hb⟩ := hi i
      refine ⟨a * b, ?_⟩
      intro j hj
      rcases Finset.mem_insert.mp hj with rfl | hj
      · rw [Submonoid.coe_mul, mul_smul, hb, smul_zero]
      · rw [Submonoid.coe_mul, mul_comm, mul_smul, ha j hj, smul_zero]
  obtain ⟨a, ha⟩ := hs Finset.univ
  exact ⟨a, fun i ↦ ha i (Finset.mem_univ i)⟩

variable (g : D →ₗ[R] M) {n : ℕ} (t : Fin n → D)
  (hspan : Submodule.span S (Set.range (fun i ↦ (1 ⊗ₜ[R] g (t i) : S ⊗[R] M))) =
    LinearMap.range (g.baseChange S))

include hspan in
/-- Finite original values detecting the local image turn its vanishing into one denominator. -/
theorem baseChange_eq_zero_iff_common_annihilator :
    g.baseChange S = 0 ↔ ∃ a : U, ∀ i, a.val • g (t i) = 0 := by
  constructor
  · intro h
    exact exists_common_annihilator U S (g ∘ t)
      (fun i ↦ (ScalarExtensionImageReduction.baseChange_eq_zero_iff g S).mp h (t i))
  · rintro ⟨a, ha⟩
    apply LinearMap.range_eq_bot.mp
    apply le_bot_iff.mp
    rw [← hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    exact (IsLocalizedModule.eq_zero_iff U (TensorProduct.mk R S M 1) (m := g (t i))).mpr
      ⟨a, ha i⟩

end FLT.Mazur.LocalizedImageFiniteWitness
