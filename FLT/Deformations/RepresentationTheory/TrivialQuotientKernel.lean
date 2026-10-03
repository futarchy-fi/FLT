/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# The kernel of a rank-two trivial quotient

An invariant surjective quotient onto the scalar field leaves a line on which
the operator acts by its determinant. No invariant complement is required.
-/

@[expose] public noncomputable section
namespace LinearMap
variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V] [Module.Finite k V]

/-- The kernel of a surjection from a two-dimensional space to the field is a line. -/
theorem finrank_ker_of_rank_two (π : V →ₗ[k] k) (hπ : Function.Surjective π)
    (hdim : Module.finrank k V = 2) : Module.finrank k (ker π) = 1 := by
  have h := π.finrank_range_add_finrank_ker
  rw [range_eq_top.mpr hπ] at h
  simp only [finrank_top, Module.finrank_self, hdim] at h
  omega

/-- An operator preserving a trivial quotient acts by its determinant on its kernel. -/
theorem apply_ker_eq_det_smul (π : V →ₗ[k] k) (hπ : Function.Surjective π)
    (hdim : Module.finrank k V = 2) (f : V →ₗ[k] V)
    (hinv : ∀ x, π (f x) = π x) (x : V) (hx : π x = 0) : f x = f.det • x := by
  let W := ker π
  have hW : W ≤ W.comap f := by
    intro y hy
    change π (f y) = 0
    exact (hinv y).trans hy
  have hquot : W.mapQ W f hW = LinearMap.id := by
    ext y
    change W.mkQ (f y) = W.mkQ y
    apply (Submodule.Quotient.eq W).mpr
    change π (f y - y) = 0
    rw [map_sub, hinv, sub_self]
  have hdet : f.det = (f.restrict hW).det := by
    rw [f.det_eq_det_mul_det W hW, hquot, LinearMap.det_id, mul_one]
  have hdimW : Module.finrank k W = 1 := finrank_ker_of_rank_two π hπ hdim
  obtain ⟨a, ha, _⟩ := (f.restrict hW).existsUnique_eq_smul_id_of_finrank_eq_one hdimW
  have hscalar : (f.restrict hW).det = a := by
    rw [ha, LinearMap.det_smul, hdimW, pow_one, LinearMap.det_id, mul_one]
  have he := DFunLike.congr_fun ha (⟨x, hx⟩ : W)
  have hv := congrArg (fun y : W ↦ (y : V)) he
  simpa only [LinearMap.restrict_apply, LinearMap.smul_apply, LinearMap.id_apply,
    Submodule.coe_smul, hdet, hscalar] using hv

end LinearMap
