/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCokernelKernelPairs

/-!
# Finite cokernel data constructed from finite generators and residual surjectivity

A finite submodule generating the full target modulo correction images gives
a finite cokernel. Surjectivity modulo the test ideal constructs divisibility
of that cokernel. The earlier frame construction then produces full reduction
matrices. These two hypotheses concern the entire target, not just its support.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteErrorReduction
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (F : M →ₗ[R] N) (I : Ideal R)
set_option quotPrecheck false
local notation "π" => (LinearMap.range F).mkQ

/-- Finite relative generators make the image of an error subspace in the full cokernel finite. -/
theorem cokernel_image_fg (H E : Submodule R N) (hE : E.FG)
    (hgen : LinearMap.range F ⊔ E = H) : (H.map π).FG := by
  have he := congrArg (Submodule.map π) hgen
  rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq] at he
  exact he ▸ hE.map π

/-- Residual correction on an error subspace gives divisibility inside the full cokernel. -/
theorem cokernel_image_le_smul (H : Submodule R N)
    (hres : LinearMap.range F ⊔ I • H = H) : H.map π ≤ I • H.map π := by
  have he := congrArg (Submodule.map π) hres
  rw [Submodule.map_sup, Submodule.mkQ_map_self, bot_sup_eq, Submodule.map_smul''] at he
  exact he.ge

/-- Compatible errors can be used without requiring surjectivity onto incompatible equations. -/
theorem exists_full_reduction_of_error_subspace (H E : Submodule R N) (hE : E.FG)
    (hgen : LinearMap.range F ⊔ E = H) (hres : LinearMap.range F ⊔ I • H = H)
    (y : N) (hy : y ∈ H) :
    ∃ (n : ℕ) (e : Fin n → N) (v : Fin n → M) (c : Fin n → Fin n → R)
      (z : M) (b : Fin n → R),
      (∀ j k, c j k ∈ I) ∧
      (∀ j, e j - F (v j) = ∑ k, c j k • e k) ∧
      y - F z = ∑ j, b j • e j :=
  exists_full_reduction F I (H.map π) (cokernel_image_fg F H E hE hgen)
    (cokernel_image_le_smul F I H hres) y (Submodule.mem_map_of_mem hy)

/-- A finite set of generators modulo correction images constructs a finite full cokernel. -/
theorem cokernel_fg_of_generators (E : Submodule R N) (hE : E.FG)
    (hgen : LinearMap.range F ⊔ E = ⊤) :
    (⊤ : Submodule R (N ⧸ LinearMap.range F)).FG := by
  have he : E.map π = ⊤ := (Submodule.map_mkQ_eq_top _ _).mpr hgen
  exact he ▸ hE.map π

/-- Surjectivity modulo the ideal makes the full cokernel divisible by that ideal. -/
theorem cokernel_le_smul_of_residual
    (hres : LinearMap.range F ⊔ I • (⊤ : Submodule R N) = ⊤) :
    (⊤ : Submodule R (N ⧸ LinearMap.range F)) ≤ I • ⊤ := by
  have he : (I • (⊤ : Submodule R N)).map π = ⊤ :=
    (Submodule.map_mkQ_eq_top _ _).mpr hres
  rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at he
  exact he.ge

/-- Finite generation modulo images and residual surjectivity construct the whole matrix. -/
theorem exists_full_reduction_of_residual (E : Submodule R N) (hE : E.FG)
    (hgen : LinearMap.range F ⊔ E = ⊤)
    (hres : LinearMap.range F ⊔ I • (⊤ : Submodule R N) = ⊤) (y : N) :
    ∃ (n : ℕ) (e : Fin n → N) (v : Fin n → M) (c : Fin n → Fin n → R)
      (z : M) (b : Fin n → R),
      (∀ j k, c j k ∈ I) ∧
      (∀ j, e j - F (v j) = ∑ k, c j k • e k) ∧
      y - F z = ∑ j, b j • e j :=
  exists_full_reduction F I ⊤ (cokernel_fg_of_generators F E hE hgen)
    (cokernel_le_smul_of_residual F I hres) y Submodule.mem_top

/-- Over a local ring, these concrete generator and residual tests give surjectivity. -/
theorem surjective_of_finite_residual [IsLocalRing R] (E : Submodule R N) (hE : E.FG)
    (hgen : LinearMap.range F ⊔ E = ⊤)
    (hres : LinearMap.range F ⊔ IsLocalRing.maximalIdeal R • (⊤ : Submodule R N) = ⊤) :
    Function.Surjective F := by
  intro y
  obtain ⟨a, z, ha, hz⟩ := exists_lift_of_finite_cokernel F (IsLocalRing.maximalIdeal R) ⊤
    (cokernel_fg_of_generators F E hE hgen)
    (cokernel_le_smul_of_residual F (IsLocalRing.maximalIdeal R) hres) y Submodule.mem_top
  have hu : IsUnit a := by
    apply IsLocalRing.notMem_maximalIdeal.mp
    intro hm
    have h1 := (IsLocalRing.maximalIdeal R).sub_mem hm ha
    rw [sub_sub_cancel] at h1
    exact (IsLocalRing.maximalIdeal.isMaximal R).ne_top ((Ideal.eq_top_iff_one _).mpr h1)
  obtain ⟨a, rfl⟩ := hu
  refine ⟨(↑a⁻¹ : R) • z, ?_⟩
  rw [map_smul, hz, smul_smul]
  simp

end FLT.Mazur.FiniteErrorReduction
