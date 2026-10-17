/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCokernelResidualLifting
public import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# Scalar extension of compatible error spaces and their relative generators

Images, sums, and finite relative generators extend to any scalar algebra.
The ambient equation module need not be finite, and no flatness is needed
for these image calculations. Residual divisibility is a separate input.
-/

@[expose] public noncomputable section
open TensorProduct
namespace FLT.Mazur.CompatibleErrorBaseChange
variable {R M N : Type*} [CommRing R]
  [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
  (S : Type*) [CommRing S] [Algebra R S]

/-- The image of an extended map is the extension of its original image. -/
theorem range_baseChange (F : M →ₗ[R] N) :
    LinearMap.range (F.baseChange S) = (LinearMap.range F).baseChange S := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    induction x using TensorProduct.inductionOn with
    | tmul s x => exact Submodule.tmul_mem_baseChange_of_mem s ⟨x, rfl⟩
    | add x y hx hy => simpa only [map_add] using Submodule.add_mem _ hx hy
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨y, ⟨x, rfl⟩, rfl⟩
    exact ⟨1 ⊗ₜ[R] x, rfl⟩

/-- Extending scalars preserves the sum used to construct compatible error spaces. -/
theorem sup_baseChange (H E : Submodule R N) :
    (H ⊔ E).baseChange S = H.baseChange S ⊔ E.baseChange S := by
  apply le_antisymm
  · rw [Submodule.baseChange_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨h, hh, e, he, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left (Submodule.tmul_mem_baseChange_of_mem 1 hh))
      (Submodule.mem_sup_right (Submodule.tmul_mem_baseChange_of_mem 1 he))
  · exact sup_le (Submodule.baseChange_mono S le_sup_left)
      (Submodule.baseChange_mono S le_sup_right)

/-- A finite original generating set extends to a finite generating set over the new scalars. -/
theorem fg_baseChange (E : Submodule R N) (hE : E.FG) : (E.baseChange S).FG := by
  obtain ⟨s, hs, rfl⟩ := Submodule.fg_def.mp hE
  rw [Submodule.baseChange_span]
  exact Submodule.fg_def.mpr ⟨_, hs.image _, rfl⟩

/-- Finite relative generators remain relative generators after scalar extension. -/
theorem relative_generators (F : M →ₗ[R] N) (H E : Submodule R N)
    (hgen : LinearMap.range F ⊔ E = H) :
    LinearMap.range (F.baseChange S) ⊔ E.baseChange S = H.baseChange S := by
  rw [range_baseChange, ← sup_baseChange, hgen]

/-- Finite relative generators construct the finite cokernel image over the new scalars. -/
theorem cokernel_image_fg (F : M →ₗ[R] N) (H E : Submodule R N)
    (hE : E.FG) (hgen : LinearMap.range F ⊔ E = H) :
    ((H.baseChange S).map (LinearMap.range (F.baseChange S)).mkQ).FG :=
  FiniteErrorReduction.cokernel_image_fg (F.baseChange S) (H.baseChange S)
    (E.baseChange S) (fg_baseChange S E hE) (relative_generators S F H E hgen)

end FLT.Mazur.CompatibleErrorBaseChange
