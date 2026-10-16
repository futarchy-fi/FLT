/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteBaseLocalizationDenominators

/-!
# Exact kernel numerators over an original multiplicative set

A finite family in localized kernels has a common original denominator and
numerators in the unlocalized kernels. Clearing the boundary error is necessary:
the first choice of fraction numerator need not be in the original kernel.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteBaseLocalizedKernels
open FiniteBaseLocalizationDenominators
variable {R : Type*} [CommRing R] (M : Submonoid R)
  {ι : Type*} [Finite ι] {A B S T : ι → Type*}
  [∀ i, CommRing (A i)] [∀ i, CommRing (B i)]
  [∀ i, CommRing (S i)] [∀ i, CommRing (T i)]
  (α : ∀ i, R →+* A i) (φ : ∀ i, A i →+* B i)
  [∀ i, Algebra (A i) (S i)] [∀ i, Algebra (B i) (T i)]
  [∀ i, IsLocalization (M.map (α i).toMonoidHom) (S i)]
  [∀ i, IsLocalization (M.map ((φ i).comp (α i)).toMonoidHom) (T i)]
  (β : ∀ i, S i →+* T i)
  (hβ : ∀ i a, β i (algebraMap _ _ a) = algebraMap _ _ (φ i a))

include hβ in
/-- Localized kernel elements have exact kernel numerators after one common denominator. -/
theorem exists_kernel_numerators (v : ∀ i, S i) (hv : ∀ i, β i (v i) = 0) :
    ∃ s : M, ∃ w : ∀ i, A i, (∀ i, φ i (w i) = 0) ∧
      ∀ i, algebraMap (A i) (S i) (w i) = algebraMap (A i) (S i) (α i s) * v i := by
  obtain ⟨s, a, ha⟩ := exists_numerators M α v
  have hb (i : ι) : algebraMap (B i) (T i) (φ i (a i)) =
      algebraMap (B i) (T i) 0 := by
    rw [← hβ i, ha i, map_mul, hv i, mul_zero, map_zero]
  obtain ⟨r, hr⟩ := exists_equalities M (fun i ↦ (φ i).comp (α i))
    (fun i ↦ φ i (a i)) (fun _ ↦ 0) hb
  refine ⟨r * s, fun i ↦ α i r * a i, ?_, ?_⟩
  · intro i
    simpa only [RingHom.comp_apply, mul_zero, map_mul] using hr i
  · intro i
    simp only [Submonoid.coe_mul, map_mul, ha i, mul_assoc]

omit [Finite ι] in
/-- Each allowed scalar is a unit in every chart localization. -/
theorem scalar_isUnit (s : M) (i : ι) :
    IsUnit (algebraMap (A i) (S i) (α i s)) :=
  IsLocalization.map_units (M := M.map (α i).toMonoidHom) (S i) ⟨α i s, ⟨s.val, s.property, rfl⟩⟩

include hβ in
omit [Finite ι] [∀ i, IsLocalization (M.map ((φ i).comp (α i)).toMonoidHom) (T i)] in
/-- A fraction with an exact kernel numerator is in the localized kernel. -/
theorem mem_kernel_of_numerator (s : M) (v : ∀ i, S i) (w : ∀ i, A i)
    (hw : ∀ i, φ i (w i) = 0)
    (he : ∀ i, algebraMap (A i) (S i) (w i) =
      algebraMap (A i) (S i) (α i s) * v i) :
    ∀ i, β i (v i) = 0 := by
  intro i
  have h := congrArg (β i) (he i)
  rw [hβ, hw i, map_zero, map_mul] at h
  exact ((scalar_isUnit M α s i).map (β i)).mul_left_cancel
    (h.symm.trans (mul_zero _).symm)

end FLT.Mazur.FiniteBaseLocalizedKernels
