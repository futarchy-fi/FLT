/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedHorizontalSmooth

/-!
# Terminal divided fibers are covered by the horizontal smooth neighborhood

When the scale, second coefficient and fourth quotient vanish, a unit
constant quotient forces the ordinate to be a unit. A unit tangent coefficient
then makes the horizontal partial a unit, in every residue characteristic.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassDilatation
universe u
variable {R S K : Type u} [CommRing R] [CommRing S] [CommRing K] [Algebra R S]
  (W : WeierstrassCurve R) (s b3 b4 b6 : R)
  (a : Coordinate W s b3 b4 b6 →ₐ[R] S)

/-- The terminal equation forces an invertible horizontal derivative after specialization. -/
theorem dividedOutput_specialized_horizontal (f : S →+* K)
    (hs : f (algebraMap R S s) = 0) (h2 : f (algebraMap R S W.a₂) = 0)
    (h4 : f (algebraMap R S b4) = 0)
    (ha : IsUnit (f (algebraMap R S W.a₁))) (h6 : IsUnit (f (algebraMap R S b6))) :
    IsUnit (f (a (dividedPartial W s b3 b4 b6 0))) := by
  let X := f (a (x W s b3 b4 b6))
  let Y := f (a (y W s b3 b4 b6))
  have he := congrArg f (equation_map W s b3 b4 b6 a)
  simp only [map_add, map_mul, map_pow, hs, h2, h4, zero_mul, zero_add] at he
  have hy : IsUnit Y := by
    apply isUnit_of_mul_isUnit_left (y := Y + f (algebraMap R S W.a₁) * X +
      f (algebraMap R S b3))
    convert h6 using 1
    dsimp [X, Y]
    linear_combination he
  rw [dividedPartial_horizontal]
  simpa only [map_sub, map_add, map_mul, map_pow, map_ofNat, AlgHom.commutes,
    hs, h2, h4, mul_zero, zero_mul, add_zero, sub_zero] using ha.mul hy

/-- Every prime on the indicated terminal fiber lies in the horizontal derivative open. -/
theorem dividedOutput_terminal_horizontal_mem (p : PrimeSpectrum S)
    (hs : algebraMap R S s ∈ p.asIdeal) (h2 : algebraMap R S W.a₂ ∈ p.asIdeal)
    (h4 : algebraMap R S b4 ∈ p.asIdeal) (ha : IsUnit W.a₁) (h6 : IsUnit b6) :
    p ∈ PrimeSpectrum.basicOpen (a (dividedPartial W s b3 b4 b6 0)) := by
  let f := Ideal.Quotient.mk p.asIdeal
  have hv := dividedOutput_specialized_horizontal W s b3 b4 b6 a f
    (Ideal.Quotient.eq_zero_iff_mem.mpr hs) (Ideal.Quotient.eq_zero_iff_mem.mpr h2)
    (Ideal.Quotient.eq_zero_iff_mem.mpr h4)
    ((ha.map (algebraMap R S)).map f) ((h6.map (algebraMap R S)).map f)
  change a (dividedPartial W s b3 b4 b6 0) ∉ p.asIdeal
  intro he
  exact hv.ne_zero (Ideal.Quotient.eq_zero_iff_mem.mpr he)

/-- The terminal fiber is actually reached by the explicit smooth neighborhood. -/
theorem dividedOutput_terminal_horizontal_range (p : PrimeSpectrum S)
    (hs : algebraMap R S s ∈ p.asIdeal) (h2 : algebraMap R S W.a₂ ∈ p.asIdeal)
    (h4 : algebraMap R S b4 ∈ p.asIdeal) (ha : IsUnit W.a₁) (h6 : IsUnit b6) :
    p ∈ Set.range (PrincipalAffineRefinement.inclusion
      (a (dividedPartial W s b3 b4 b6 0))) := by
  rw [PrincipalAffineRefinement.range_inclusion]
  exact dividedOutput_terminal_horizontal_mem W s b3 b4 b6 a p hs h2 h4 ha h6

end FLT.Mazur.WeierstrassDilatation
