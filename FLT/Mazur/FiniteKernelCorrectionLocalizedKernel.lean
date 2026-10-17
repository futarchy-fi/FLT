/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteKernelCorrectionLocalization
public import Mathlib.Algebra.Module.LocalizedModule.Exact

/-!
# The full kernel image after localization in original scalars

Localization of the finite ambient synthesis still covers the entire
localized restriction kernel. Consequently its correction operator has
exactly the full localized kernel-difference image, even when the ambient
source is not finite as a module over the original invariant scalars.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FiniteKernelCorrections
variable {R : Type*} [CommRing R] (U : Submonoid R)
  {M N P : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup P] [Module R P]

/-- Composition is preserved by the explicit localized operator. -/
theorem localizedMap_comp (F : M →ₗ[R] N) (G : N →ₗ[R] P) :
    localizedMap U (G.comp F) = (localizedMap U G).comp (localizedMap U F) := by
  ext v
  induction v using LocalizedModule.induction_on with
  | _ x s => simp only [localizedMap_mk, LinearMap.comp_apply]

variable {Q T C : Type*} [CommRing Q] [CommRing T] [CommRing C]
  [Algebra R Q] [Algebra R T] [Algebra R C]
  {n : ℕ} (z : Fin n → Q) (r : Q →ₐ[R] T)
  (hz : Ideal.span (Set.range z) = RingHom.ker r.toRingHom)
include hz

/-- Finite ambient synthesis remains exact onto the entire localized boundary kernel. -/
theorem localized_synthesis_range :
    LinearMap.range (localizedMap U (synthesis R z)) =
      LinearMap.ker (localizedMap U r.toLinearMap) := by
  have he : Function.Exact (synthesis R z) r.toLinearMap :=
    LinearMap.exact_iff.mpr (synthesis_range R z r hz).symm
  exact (LinearMap.exact_iff.mp (LocalizedModule.map_exact U _ _ he)).symm

/-- Every localized boundary-kernel element has one localized finite coefficient tuple. -/
theorem localized_kernel_coordinates (x : LocalizedModule U Q) :
    localizedMap U r.toLinearMap x = 0 ↔
      ∃ v : LocalizedModule U (Fin n → Q), localizedMap U (synthesis R z) v = x := by
  change x ∈ LinearMap.ker (localizedMap U r.toLinearMap) ↔ _
  rw [← localized_synthesis_range U z r hz, LinearMap.mem_range]

/-- The finite operator retains the full kernel-difference image after scalar localization. -/
theorem localized_operator_range (p q : Q →ₐ[R] C) :
    LinearMap.range (localizedMap U (operator R z p q)) =
      Submodule.map (localizedMap U (p.toLinearMap - q.toLinearMap))
        (LinearMap.ker (localizedMap U r.toLinearMap)) := by
  rw [operator, localizedMap_comp, LinearMap.range_comp,
    localized_synthesis_range U z r hz]

end FLT.Mazur.FiniteKernelCorrections
