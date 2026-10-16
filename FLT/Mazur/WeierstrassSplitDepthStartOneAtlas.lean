/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedStartOneAtlas
public import FLT.Mazur.WeierstrassNodalDividedDepth

/-!
# Constructing the depth-one arithmetic atlas from split-node coefficients

Strictly before the middle depth, the original coefficient conditions
construct all division data and all arithmetic atlas hypotheses. Starting
at one is a choice of this construction, not an assertion about arbitrary
pre-existing modification schemes.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {depth : ℕ} (D : SplitNodeDepth W π depth)
  (n : ℕ) (hn : 2 * (1 + n) < depth)

/-- The original split depth supplies an actual bounded family starting at depth one. -/
def splitDepthStartOneData (i : Fin (n + 1)) : Data W π (1 + i.val) :=
  Classical.choice (nodalDepth_exists_data D.maximalIdeal_eq (by have := hn; have := i.isLt; omega)
    D.a₃_mem D.a₄_mem D.a₆_mem)

/-- All arithmetic coefficient hypotheses follow from the strict original depth bound. -/
theorem splitDepthStartOneAtlasCoefficients :
    ArithmeticAtlasCoefficients (splitDepthStartOneData D n hn) where
  a1_unit := D.a₁_unit
  scale_div := by simp
  a2_div := by
    simpa only [D.maximalIdeal_eq, Ideal.mem_span_singleton] using D.a₂_mem
  b3_div i := by
    have h := nodalDepth_linear_mem D.uniformizer_ne_zero D.maximalIdeal_eq
      (splitDepthStartOneData D n hn i) (by have := i.isLt; omega) D.a₃_mem D.a₄_mem
    simpa only [D.maximalIdeal_eq, Ideal.mem_span_singleton] using h.1
  b4_div i := by
    have h := nodalDepth_linear_mem D.uniformizer_ne_zero D.maximalIdeal_eq
      (splitDepthStartOneData D n hn i) (by have := i.isLt; omega) D.a₃_mem D.a₄_mem
    simpa only [D.maximalIdeal_eq, Ideal.mem_span_singleton] using h.2
  b6_div i := by
    have h := nodalDepth_constant_mem D.uniformizer_ne_zero D.maximalIdeal_eq
      (splitDepthStartOneData D n hn i) (by have := i.isLt; omega) D.a₆_mem
    simpa only [D.maximalIdeal_eq, Ideal.mem_span_singleton] using h

/-- Every independently supplied quotient at the same depth is the constructed one. -/
theorem splitDepthStartOneData_eq (i : Fin (n + 1)) (d : Data W π (1 + i.val)) :
    splitDepthStartOneData D n hn i = d := Data.unique D.uniformizer_ne_zero _ _

end FLT.Mazur.WeierstrassDividedDepth
