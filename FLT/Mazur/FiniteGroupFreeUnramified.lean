/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupOrbitTensorDetection
public import Mathlib.RingTheory.Unramified.Finite

/-!
# Full differential rigidity of free finite-group quotients

The orbit separator lifts to a separability tensor. Injectivity of the full
orbit comparison proves its annihilation identities before passing to any
residue field. Thus the fixed-ring inclusion is formally unramified, even
in wild characteristic and for nonreduced sources.
-/

@[expose] public noncomputable section
open TensorProduct
open scoped BigOperators
namespace FLT.Mazur.FiniteGroupQuotient
variable (G : Type*) [Group G] [Fintype G]
  (A : Type*) [CommRing A] [MulSemiringAction G A]
local notation "S" => invariantRing G A
local notation "C" => A ⊗[S] A
variable (hfree : ∀ g : G, g ≠ 1 → fixedPointIdeal G A g = ⊤)
include hfree

omit [Fintype G] in
/-- Freeness constructs a tensor whose only nonzero orbit coordinate is the identity. -/
theorem exists_identity_orbit_tensor [Finite G] :
    ∃ t : C, orbitTensorCoordinate G A 1 t = 1 ∧
      ∀ g : G, g ≠ 1 → orbitTensorCoordinate G A g t = 0 := by
  classical
  let _ := Fintype.ofFinite G
  obtain ⟨v, hv, hv₁, hv₀⟩ := exists_identity_orbit_combination G A hfree
  obtain ⟨c, hc⟩ := Finsupp.mem_span_range_iff_exists_finsupp.mp hv
  let t : C := ∑ b ∈ c.support, c b ⊗ₜ[S] b
  have ht (g : G) : orbitTensorCoordinate G A g t = v g := by
    simpa only [t, map_sum, orbitTensorCoordinate_tmul, Finsupp.sum,
      Finset.sum_apply, Pi.smul_apply, smul_eq_mul, orbitProfile] using congrFun hc g
  exact ⟨t, (ht 1).trans hv₁, fun g hg ↦ (ht g).trans (hv₀ g hg)⟩

omit [Fintype G] in
/-- The constructed tensor kills every full diagonal equation and has multiplication one. -/
theorem exists_free_separability_tensor [Finite G] :
    ∃ t : C, (∀ a : A, (1 ⊗ₜ[S] a - a ⊗ₜ[S] 1) * t = 0) ∧
      Algebra.TensorProduct.lmul' S t = 1 := by
  obtain ⟨t, ht₁, ht₀⟩ := exists_identity_orbit_tensor G A hfree
  refine ⟨t, fun a ↦ ?_, ?_⟩
  · apply orbitTensorCoordinate_ext G A hfree
    intro g
    rw [map_mul, map_sub, map_zero, orbitTensorCoordinate_tmul,
      orbitTensorCoordinate_tmul]
    by_cases hg : g = 1
    · subst g
      rw [one_smul, one_smul, one_mul, mul_one, sub_self, zero_mul]
    · rw [ht₀ g hg, mul_zero]
  · have he : orbitTensorCoordinate G A 1 = Algebra.TensorProduct.lmul' S := by
      apply AlgHom.ext
      intro x
      induction x using TensorProduct.inductionOn with
      | tmul a b =>
        simp only [orbitTensorCoordinate_tmul, one_smul,
          Algebra.TensorProduct.lmul'_apply_tmul]
      | add x y hx hy => simp only [map_add, hx, hy]
    rw [← he]
    exact ht₁

omit [Fintype G] in
/-- A free finite action kills all differentials over its actual fixed ring. -/
theorem invariant_formallyUnramified [Finite G] : Algebra.FormallyUnramified S A := by
  let _ := Fintype.ofFinite G
  let _ := invariant_module_finite G hfree
  exact Algebra.FormallyUnramified.iff_exists_tensorProduct.mpr
    (exists_free_separability_tensor G A hfree)

end FLT.Mazur.FiniteGroupQuotient
