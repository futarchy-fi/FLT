/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# A rank-two frame from a surjective quotient

A quotient functional constructs its kernel basis and a lift of one. This
requires neither a chosen subcharacter nor a splitting of the representation.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.Extensions
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] (π : V →ₗ[k] k) (hπ : Function.Surjective π)
  (hdim : Module.finrank k V = 2)

include hπ hdim in
/-- The kernel of the given surjective rank-two quotient is one-dimensional. -/
theorem quotient_kernel_finrank : Module.finrank k (LinearMap.ker π) = 1 := by
  have hq : Module.finrank k (V ⧸ LinearMap.ker π) = 1 := by
    rw [(π.quotKerEquivOfSurjective hπ).finrank_eq, Module.finrank_self]
  have h := (LinearMap.ker π).finrank_quotient_add_finrank
  rw [hq, hdim] at h
  omega

/-- A basis of the actual kernel, constructed from its dimension. -/
def quotientKernelEquiv : k ≃ₗ[k] LinearMap.ker π :=
  LinearEquiv.ofFinrankEq _ _ ((Module.finrank_self k).trans
    (quotient_kernel_finrank π hπ hdim).symm)

/-- Combine the kernel coordinate with a chosen lift of one. -/
def quotientFrameMap : (Fin 2 → k) →ₗ[k] V :=
  ((LinearMap.ker π).subtype.comp (quotientKernelEquiv π hπ hdim).toLinearMap).comp
      (LinearMap.proj 0) +
    (LinearMap.toSpanSingleton k V (hπ 1).choose).comp (LinearMap.proj 1)

/-- The second coordinate is the original quotient functional. -/
theorem quotientFrameMap_projection (v : Fin 2 → k) :
    π (quotientFrameMap π hπ hdim v) = v 1 := by
  change π ((quotientKernelEquiv π hπ hdim (v 0) : V) + v 1 • (hπ 1).choose) = _
  rw [map_add, map_smul, (hπ 1).choose_spec]
  have h := (quotientKernelEquiv π hπ hdim (v 0)).property
  change π _ = 0 at h
  simp [h]

/-- The constructed frame is bijective by the actual quotient's kernel. -/
theorem quotientFrameMap_bijective : Function.Bijective (quotientFrameMap π hπ hdim) := by
  constructor
  · intro v w h
    have h1 : v 1 = w 1 := by
      simpa only [quotientFrameMap_projection] using congrArg π h
    have h0 : v 0 = w 0 := by
      apply (quotientKernelEquiv π hπ hdim).injective
      apply Subtype.ext
      change (quotientKernelEquiv π hπ hdim (v 0) : V) + v 1 • (hπ 1).choose =
        (quotientKernelEquiv π hπ hdim (w 0) : V) + w 1 • (hπ 1).choose at h
      rw [h1] at h
      exact add_right_cancel h
    funext i
    fin_cases i <;> assumption
  · intro x
    let y : LinearMap.ker π := ⟨x - π x • (hπ 1).choose, by
      simp [LinearMap.mem_ker, (hπ 1).choose_spec]⟩
    refine ⟨![(quotientKernelEquiv π hπ hdim).symm y, π x], ?_⟩
    change (quotientKernelEquiv π hπ hdim ((quotientKernelEquiv π hπ hdim).symm y) : V) +
      π x • (hπ 1).choose = x
    rw [LinearEquiv.apply_symm_apply]
    exact sub_add_cancel _ _

/-- A frame adapted to the given quotient, constructed without residual row data. -/
def surjectiveQuotientFrame : (Fin 2 → k) ≃ₗ[k] V :=
  LinearEquiv.ofBijective (quotientFrameMap π hπ hdim) (quotientFrameMap_bijective π hπ hdim)

/-- Its inverse recovers the original quotient coordinate. -/
theorem surjectiveQuotientFrame_symm_one (x : V) :
    (surjectiveQuotientFrame π hπ hdim).symm x 1 = π x := by
  have h := quotientFrameMap_projection π hπ hdim ((surjectiveQuotientFrame π hπ hdim).symm x)
  change π (surjectiveQuotientFrame π hπ hdim ((surjectiveQuotientFrame π hπ hdim).symm x)) = _ at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h.symm

end GaloisRepresentation.Extensions
