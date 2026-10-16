/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonSmoothingLocalizedPolynomials
public import FLT.Mazur.PolygonSmoothingScalingNaturality
public import Mathlib.Algebra.BigOperators.Fin

/-!
# The original reciprocal action on node polynomial representatives

Coefficient change and the actual unit action act on every polynomial term.
The explicit node denominator becomes (1-a*x)(1-a⁻¹*y), so it is not silently
identified with the unscaled denominator.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S]
variable (f : R →+* S) (t : R) (s : S) (hs : f t = s) (a : Sˣ)

/-- Coefficient change followed by the original reciprocal scaling on the full chart. -/
def scaledNodeRingMap : ChartRing t →+* ChartRing s :=
  (reciprocalScale s a).toRingHom.comp (ringMap f t s hs)

/-- Literal polynomial substitution retaining every coefficient and the given unit. -/
def scaledNodePolynomialMap : MvPolynomial (Fin 2) R →+* MvPolynomial (Fin 2) S :=
  MvPolynomial.eval₂Hom (MvPolynomial.C.comp f)
    ![MvPolynomial.C (a : S) * MvPolynomial.X 0,
      MvPolynomial.C (↑a⁻¹ : S) * MvPolynomial.X 1]

/-- The substitution is exactly the original arithmetic chart action on representatives. -/
theorem scaledNodePolynomialMap_mk (p : MvPolynomial (Fin 2) R) :
    Ideal.Quotient.mk (relationIdeal s) (scaledNodePolynomialMap f a p) =
      scaledNodeRingMap f t s hs a (Ideal.Quotient.mk (relationIdeal t) p) := by
  have he : (Ideal.Quotient.mk (relationIdeal s)).comp (scaledNodePolynomialMap f a) =
      (scaledNodeRingMap f t s hs a).comp (Ideal.Quotient.mk (relationIdeal t)) := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp only [RingHom.comp_apply, scaledNodePolynomialMap, MvPolynomial.eval₂Hom_C,
        scaledNodeRingMap]
      change algebraMap S (ChartRing s) (f r) =
        reciprocalScale s a (ringMap f t s hs (algebraMap R (ChartRing t) r))
      rw [ringMap_scalar, AlgHom.commutes]
    · intro k
      fin_cases k
      · simp only [RingHom.comp_apply, scaledNodePolynomialMap, MvPolynomial.eval₂Hom_X',
          scaledNodeRingMap]
        change algebraMap S (ChartRing s) (a : S) * leftCoordinate s =
          reciprocalScale s a (ringMap f t s hs (leftCoordinate t))
        rw [ringMap_left, reciprocalScale_left]
      · simp only [RingHom.comp_apply, scaledNodePolynomialMap, MvPolynomial.eval₂Hom_X',
          scaledNodeRingMap]
        change algebraMap S (ChartRing s) (↑a⁻¹ : S) * rightCoordinate s =
          reciprocalScale s a (ringMap f t s hs (rightCoordinate t))
        rw [ringMap_right, reciprocalScale_right]
  exact DFunLike.congr_fun he p

/-- The actual action preserves the two separate factors of the node denominator. -/
theorem scaledNodeRingMap_denominator :
    scaledNodeRingMap f t s hs a (nodeMarkingDenominator t) =
      (1 - algebraMap S (ChartRing s) (a : S) * leftCoordinate s) *
        (1 - algebraMap S (ChartRing s) (↑a⁻¹ : S) * rightCoordinate s) := by
  rw [nodeMarkingDenominator, map_mul,
    RingHom.map_sub (scaledNodeRingMap f t s hs a) 1 (leftCoordinate t),
    RingHom.map_sub (scaledNodeRingMap f t s hs a) 1 (rightCoordinate t), map_one]
  change (1 - reciprocalScale s a (ringMap f t s hs (leftCoordinate t))) *
    (1 - reciprocalScale s a (ringMap f t s hs (rightCoordinate t))) = _
  rw [ringMap_left, ringMap_right, reciprocalScale_left, reciprocalScale_right]

/-- The polynomial denominator itself has the corresponding literal scaled expression. -/
theorem scaledNodePolynomialMap_denominator :
    scaledNodePolynomialMap f a (nodeMarkingDenominatorPolynomial (R := R)) =
      (1 - MvPolynomial.C (a : S) * MvPolynomial.X 0) *
        (1 - MvPolynomial.C (↑a⁻¹ : S) * MvPolynomial.X 1) := by
  simp only [nodeMarkingDenominatorPolynomial, map_mul, map_sub, map_one,
    scaledNodePolynomialMap, MvPolynomial.eval₂Hom_X',
    Matrix.cons_val_zero, Matrix.cons_val_one]

/-- Every original coefficient contributes with its actual reciprocal monomial weight. -/
theorem scaledNodePolynomialMap_sum (p : MvPolynomial (Fin 2) R) :
    scaledNodePolynomialMap f a p =
      ∑ d ∈ p.support, MvPolynomial.C (f (p.coeff d)) *
        (MvPolynomial.C (a : S) * MvPolynomial.X 0) ^ d 0 *
        (MvPolynomial.C (↑a⁻¹ : S) * MvPolynomial.X 1) ^ d 1 := by
  change MvPolynomial.eval₂ _ _ p = _
  rw [MvPolynomial.eval₂_eq']
  apply Finset.sum_congr rfl
  intro d _
  simp only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    RingHom.comp_apply, mul_assoc]

end FLT.Mazur.PolygonSmoothing
