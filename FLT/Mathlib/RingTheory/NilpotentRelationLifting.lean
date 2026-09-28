/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.Module.Projective
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Lifting relations across a nilpotent base ideal

For a surjection onto a projective module, generators of its kernel modulo a
nilpotent base ideal generate the entire kernel. No finite generation of the
source or kernel is needed.
-/

@[expose] public noncomputable section

namespace Submodule

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- Nakayama's conclusion for a nilpotent ideal needs no finiteness hypothesis. -/
theorem le_of_le_sup_smul_of_isNilpotent {I : Ideal R} (hI : IsNilpotent I)
    {J K : Submodule R M} (h : K ≤ J ⊔ I • K) : K ≤ J := by
  have hn (n : ℕ) : K ≤ J ⊔ I ^ n • K := by
    induction n with
    | zero => simp
    | succ n ih =>
      calc
        K ≤ J ⊔ I • K := h
        _ ≤ J ⊔ I • (J ⊔ I ^ n • K) :=
          sup_le_sup_left (smul_mono_right I ih) J
        _ = J ⊔ (I • J ⊔ I ^ (n + 1) • K) := by
          rw [smul_sup, ← Submodule.mul_smul, ← pow_succ']
        _ ≤ J ⊔ I ^ (n + 1) • K :=
          sup_le le_sup_left (sup_le (smul_le_right.trans le_sup_left) le_sup_right)
  obtain ⟨n, hn0⟩ := hI
  simpa [hn0] using hn n

end Submodule

namespace LinearMap

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [AddCommGroup N]
  [Module R M] [Module R N] [Module.Projective R N]

/-- Relations modulo a nilpotent base ideal lift along a surjection onto a
projective module, even when the kernel is not finitely generated. -/
theorem ker_eq_of_le_sup_smul_of_isNilpotent (f : M →ₗ[R] N)
    (hf : Function.Surjective f) {I : Ideal R} (hI : IsNilpotent I)
    {J : Submodule R M} (hJ : J ≤ f.ker)
    (h : f.ker ≤ J ⊔ I • (⊤ : Submodule R M)) : f.ker = J := by
  obtain ⟨s, hs⟩ := f.exists_rightInverse_of_surjective (range_eq_top.mpr hf)
  let r : M →ₗ[R] M := LinearMap.id - s.comp f
  have hr (x : M) (hx : x ∈ f.ker) : r x = x := by
    simp [r, mem_ker.mp hx]
  have hrr : r.range ≤ f.ker := by
    rintro _ ⟨x, rfl⟩
    change f (x - s (f x)) = 0
    have hsx := LinearMap.congr_fun hs (f x)
    simpa using sub_eq_zero.mpr hsx.symm
  apply le_antisymm ?_ hJ
  apply Submodule.le_of_le_sup_smul_of_isNilpotent hI
  intro x hx
  have hxmap : r x ∈ (J ⊔ I • (⊤ : Submodule R M)).map r :=
    Submodule.mem_map_of_mem (h hx)
  rw [Submodule.map_sup, Submodule.map_smul'', Submodule.map_top] at hxmap
  rw [hr x hx] at hxmap
  apply (sup_le_sup ?_ (smul_mono_right I hrr)) hxmap
  rintro _ ⟨y, hy, rfl⟩
  rwa [hr y (hJ hy)]

end LinearMap

namespace AlgHom

variable {R S A : Type*} [CommRing R] [CommRing S] [CommRing A]
  [Algebra R S] [Algebra R A] [Module.Projective R A]

/-- An ideal generates all relations if it does so modulo a nilpotent ideal
of the base and the target algebra is projective over the base. -/
theorem ker_eq_of_le_sup_map_of_isNilpotent (f : S →ₐ[R] A)
    (hf : Function.Surjective f) {I : Ideal R} (hI : IsNilpotent I)
    {J : Ideal S} (hJ : J ≤ RingHom.ker f)
    (h : RingHom.ker f ≤ J ⊔ I.map (algebraMap R S)) : RingHom.ker f = J := by
  have he := f.toLinearMap.ker_eq_of_le_sup_smul_of_isNilpotent hf hI
    (J := J.restrictScalars R) hJ (by
      rw [Ideal.smul_top_eq_map]
      intro x hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.mp (h hx)
      exact Submodule.mem_sup.mpr ⟨y, hy, z, hz, rfl⟩)
  apply SetLike.coe_injective
  exact congrArg (fun K : Submodule R S ↦ (K : Set S)) he

end AlgHom
