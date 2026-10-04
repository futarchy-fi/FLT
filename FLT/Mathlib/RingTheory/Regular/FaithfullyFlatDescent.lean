/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra

/-! # Faithfully flat reflection of regular sequences -/

@[expose] public noncomputable section

open scoped TensorProduct

namespace RingTheory.Sequence

variable {R S M N : Type*} [CommRing R] [CommRing S] [Algebra R S]
  [Module.FaithfullyFlat R S] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- A faithfully flat base-change comparison is injective on the original module. -/
theorem baseChange_injective_of_faithfullyFlat {f : M →ₗ[R] N} (hf : IsBaseChange S f) :
    Function.Injective f := by
  intro m n h
  apply Module.FaithfullyFlat.tensorProduct_mk_injective (A := R) (B := S) M
  apply hf.equiv.injective
  change hf.equiv (1 ⊗ₜ[R] m) = hf.equiv (1 ⊗ₜ[R] n)
  simpa only [hf.equiv_tmul, one_smul] using h

/-- Regularity of an element descends along the specified faithfully flat base change. -/
theorem isSMulRegular_of_faithfullyFlat_baseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {x : R} (h : IsSMulRegular N (algebraMap R S x)) : IsSMulRegular M x := by
  apply IsSMulRegular.of_right_eq_zero_of_smul
  intro m hm
  apply baseChange_injective_of_faithfullyFlat hf
  have hz : algebraMap R S x • f m = 0 := by
    rw [algebraMap_smul, ← f.map_smul, hm, map_zero]
  simpa only [map_zero] using h.right_eq_zero_of_smul hz

/-- Weak regularity descends, including all successive quotient injectivity conditions. -/
theorem IsWeaklyRegular.of_faithfullyFlat_baseChange {f : M →ₗ[R] N}
    (hf : IsBaseChange S f) {rs : List R}
    (h : IsWeaklyRegular N (rs.map (algebraMap R S))) : IsWeaklyRegular M rs := by
  induction rs generalizing M N with
  | nil => simp
  | cons x rs ih =>
    simp only [List.map_cons, isWeaklyRegular_cons_iff] at h ⊢
    let e := (QuotSMulTop.algebraMapTensorEquivTensorQuotSMulTop x M S).symm ≪≫ₗ
      QuotSMulTop.congr ((algebraMap R S) x) hf.equiv
    have hg : IsBaseChange S <|
        e.toLinearMap.restrictScalars R ∘ₗ TensorProduct.mk R S (QuotSMulTop x M) 1 :=
      IsBaseChange.of_equiv e (fun _ ↦ by simp)
    exact ⟨isSMulRegular_of_faithfullyFlat_baseChange hf h.1, ih hg h.2⟩

/-- Faithful flatness also reflects the nonzero terminal quotient of a regular sequence. -/
theorem IsRegular.of_faithfullyFlat_baseChange {f : M →ₗ[R] N} (hf : IsBaseChange S f)
    {rs : List R} (h : IsRegular N (rs.map (algebraMap R S))) : IsRegular M rs := by
  refine ⟨h.1.of_faithfullyFlat_baseChange hf, ?_⟩
  have hn : (Ideal.ofList rs).map (algebraMap R S) • (⊤ : Submodule S N) ≠ ⊤ := by
    rw [Ideal.map_ofList]
    exact h.2.symm
  exact ((hf.map_smul_top_ne_top_iff_of_faithfullyFlat R M _).mp hn).symm

/-- Regularity can be tested after a faithfully flat algebra extension. -/
theorem isRegular_iff_of_faithfullyFlat {rs : List R} :
    IsRegular S (rs.map (algebraMap R S)) ↔ IsRegular R rs :=
  ⟨fun h ↦ h.of_faithfullyFlat_baseChange (IsBaseChange.linearMap R S),
    fun h ↦ h.of_faithfullyFlat⟩

end RingTheory.Sequence
