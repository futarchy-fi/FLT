/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.RingTheory.Ideal.Maps

/-! # Kernels of coefficient maps on multivariate polynomials -/

@[expose] public noncomputable section

namespace MvPolynomial

variable {R S ι : Type*} [CommRing R] [CommRing S]

/-- The kernel of a coefficient map is the extension of the coefficient kernel. -/
theorem ker_map_eq_map_C (f : R →+* S) :
    RingHom.ker (map (σ := ι) f) = (RingHom.ker f).map C := by
  classical
  apply le_antisymm
  · intro g hg
    have hc (d : ι →₀ ℕ) : f (g.coeff d) = 0 := by
      have h := congrArg (fun h : MvPolynomial ι S ↦ h.coeff d) (show map f g = 0 from hg)
      simpa [coeff_map] using h
    rw [g.as_sum]
    apply Submodule.sum_mem
    intro d hd
    have hm : C (g.coeff d) ∈ (RingHom.ker f).map (C (σ := ι)) :=
      Ideal.mem_map_of_mem C (hc d)
    simpa only [C_mul_monomial, mul_one] using
      ((RingHom.ker f).map C).mul_mem_right (monomial d 1) hm
  · apply Ideal.map_le_iff_le_comap.mpr
    intro r hr
    change map f (C r) = 0
    simp only [map_C, show f r = 0 from hr, map_zero]

end MvPolynomial
