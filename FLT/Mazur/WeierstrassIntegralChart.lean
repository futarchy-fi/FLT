/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.EllipticCurve.Projective.Basic
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Integral affine charts of the Weierstrass cubic

The chart with coordinate j equal to one is the polynomial algebra modulo the
homogeneous cubic and X_j - 1. Evaluation is constructed from actual normalized
solutions, and commutes with every coefficient-preserving ring map.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.WeierstrassIntegralChart

open MvPolynomial

variable {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
  [Algebra R S] [Algebra R T] (W : WeierstrassCurve R) (j : Fin 3)

/-- The cubic relation and the normalization of the selected projective coordinate. -/
def relations : Ideal (MvPolynomial (Fin 3) R) :=
  Ideal.span {W.toProjective.polynomial, X j - 1}

/-- The actual affine coordinate algebra, including the chart containing infinity. -/
abbrev Coordinate := MvPolynomial (Fin 3) R ⧸ relations W j

/-- The universal normalized projective coordinates. -/
def coord (i : Fin 3) : Coordinate W j := Ideal.Quotient.mk _ (X i)

/-- A normalized solution of the cubic defines evaluation on its chart algebra. -/
def evaluation (v : Fin 3 → S)
    (hv : (W.map (algebraMap R S)).toProjective.Equation v) (hj : v j = 1) :
    Coordinate W j →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ (aeval v) (by
    change relations W j ≤ RingHom.ker (aeval v).toRingHom
    apply Ideal.span_le.mpr
    intro f hf
    rcases Set.mem_insert_iff.mp hf with rfl | hf
    · change aeval v W.toProjective.polynomial = 0
      simpa only [WeierstrassCurve.Projective.Equation,
        WeierstrassCurve.Projective.map_polynomial, eval_map, ← aeval_def] using hv
    · have hf' : f = X j - 1 := Set.mem_singleton_iff.mp hf
      subst f
      change aeval v (X j - 1) = 0
      simp only [map_sub, aeval_X, map_one, hj, sub_self])

/-- Evaluation has the prescribed coordinate values. -/
@[simp] theorem evaluation_coord (v : Fin 3 → S)
    (hv : (W.map (algebraMap R S)).toProjective.Equation v) (hj : v j = 1)
    (i : Fin 3) : evaluation W j v hv hj (coord W j i) = v i := by
  exact aeval_X v i

/-- The normalized coordinate is one in the chart algebra itself. -/
@[simp] theorem coord_self : coord W j j = 1 := by
  apply sub_eq_zero.mp
  change Ideal.Quotient.mk (relations W j) (X j) - Ideal.Quotient.mk _ 1 = 0
  rw [← map_sub, Ideal.Quotient.eq_zero_iff_mem]
  exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))

/-- The universal coordinates satisfy the original cubic after scalar extension. -/
theorem coord_equation :
    (W.map (algebraMap R (Coordinate W j))).toProjective.Equation (coord W j) := by
  change eval (coord W j) (W.map _).toProjective.polynomial = 0
  rw [WeierstrassCurve.Projective.map_polynomial, eval_map, ← aeval_def]
  have he : aeval (coord W j) = Ideal.Quotient.mkₐ R (relations W j) := by
    ext i
    exact aeval_X (coord W j) i
  rw [he]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_insert _ _))

/-- Maps from a chart algebra are determined by the projective coordinates. -/
@[ext] theorem hom_ext (f g : Coordinate W j →ₐ[R] S)
    (h : ∀ i, f (coord W j i) = g (coord W j i)) : f = g := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  exact h

/-- Evaluation commutes with an algebra map, in particular residue reduction. -/
theorem evaluation_natural (v : Fin 3 → S)
    (hv : (W.map (algebraMap R S)).toProjective.Equation v) (hj : v j = 1)
    (f : S →ₐ[R] T)
    (hw : (W.map (algebraMap R T)).toProjective.Equation (f ∘ v))
    (hk : (f ∘ v) j = 1) :
    f.comp (evaluation W j v hv hj) = evaluation W j (f ∘ v) hw hk := by
  apply hom_ext
  intro i
  simp only [AlgHom.comp_apply, evaluation_coord, Function.comp_apply]

end FLT.Mazur.WeierstrassIntegralChart
