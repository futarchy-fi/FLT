/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteErrorReducedInclusion
public import FLT.Mazur.CompatibleErrorBaseChange

/-!
# Residue tests on the actual scalar-extended image

The image after localization is formed over the local scalar ring before
reduction. Its finiteness, reduction injectivity, and residual vanishing are
kept separate. Residual vanishing can be checked on original pure tensors.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.ScalarExtensionImageReduction
variable {R D M : Type*} [CommRing R]
  [AddCommGroup D] [Module R D] [AddCommGroup M] [Module R M]
  (g : D →ₗ[R] M) (S : Type*) [CommRing S] [Algebra R S]

/-- The scalar-extended image is finite when the original image has actual finite generators. -/
theorem range_fg (hfg : (LinearMap.range g).FG) : (LinearMap.range (g.baseChange S)).FG := by
  rw [CompatibleErrorBaseChange.range_baseChange]
  exact CompatibleErrorBaseChange.fg_baseChange S _ hfg

/-- Original unit pure tensors test vanishing of the full scalar-extended map. -/
theorem baseChange_eq_zero_iff :
    g.baseChange S = 0 ↔ ∀ t, (1 ⊗ₜ[R] g t : S ⊗[R] M) = 0 := by
  constructor
  · intro h t
    exact congrArg (fun F : (S ⊗[R] D) →ₗ[S] S ⊗[R] M ↦ F (1 ⊗ₜ[R] t)) h
  · intro h
    apply LinearMap.ext
    intro x
    change g.baseChange S x = 0
    induction x using TensorProduct.inductionOn with
    | tmul s t =>
      change s ⊗ₜ[R] g t = 0
      simpa only [smul_tmul', smul_eq_mul, mul_one, smul_zero] using congrArg (s • ·) (h t)
    | add x y hx hy => rw [map_add, hx, hy, add_zero]

/-- Residual vanishing of original unit tensors controls the full image over the new ring. -/
theorem range_le_smul_top_iff (J : Ideal S) :
    LinearMap.range (g.baseChange S) ≤ J • (⊤ : Submodule S (S ⊗[R] M)) ↔
      ∀ t, (1 ⊗ₜ[R] g t : S ⊗[R] M) ∈ J • (⊤ : Submodule S (S ⊗[R] M)) := by
  constructor
  · intro h t
    exact h ⟨1 ⊗ₜ[R] t, rfl⟩
  · intro h x hx
    obtain ⟨x, rfl⟩ := hx
    induction x using TensorProduct.inductionOn with
    | tmul s t =>
      change s ⊗ₜ[R] g t ∈ _
      simpa only [smul_tmul', smul_eq_mul, mul_one] using
        (J • (⊤ : Submodule S (S ⊗[R] M))).smul_mem s (h t)
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy

/-- Nakayama applies to the actual local image after its own reduction kernel is retained. -/
theorem baseChange_eq_zero_of_reduction [IsLocalRing S]
    (hfg : (LinearMap.range (g.baseChange S)).FG)
    (hinj : Function.Injective (SubmoduleReduction.inclusion (IsLocalRing.maximalIdeal S)
      (LinearMap.range (g.baseChange S))))
    (hres : ∀ t, (1 ⊗ₜ[R] g t : S ⊗[R] M) ∈
      IsLocalRing.maximalIdeal S • (⊤ : Submodule S (S ⊗[R] M))) :
    g.baseChange S = 0 :=
  LinearMap.range_eq_bot.mp (FiniteErrorReduction.eq_bot_of_reduced_inclusion _ hfg hinj
    ((range_le_smul_top_iff g S _).mpr hres))

end FLT.Mazur.ScalarExtensionImageReduction
