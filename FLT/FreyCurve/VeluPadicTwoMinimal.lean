/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluPadicIntegralAway
public import FLT.FreyCurve.VeluTargetGeometry
public import FLT.Mazur.EllipticUnitInvariantsReduction
public import FLT.Mazur.PadicValuationArithmetic

/-!
# The canonical actual target equation is already minimal at two

Vélu preserves a₁ = 1. On the integral equation at two this makes c₄ a unit,
so the canonical target is minimal and semistable before any torsion point
is used. No change of variables is needed at this place.
-/

@[expose] public section

namespace FreyPackage

open WeierstrassCurve FLT.Mazur IsLocalRing

attribute [local instance] padicIntegerSubring_isDiscreteValuationRing

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- The actual canonical target has an integral equation with unit c₄ at two. -/
theorem IsVeluTarget.exists_padic_two_unit_model (h : P.IsVeluTarget E) :
    ∃ W : WeierstrassCurve (padicIntegerSubring 2),
      W.map (algebraMap (padicIntegerSubring 2) ℚ_[2]) = E.map (algebraMap ℚ ℚ_[2]) ∧
        IsUnit W.c₄ := by
  have h2p : 2 ≠ P.p := by have := P.hp5; omega
  obtain ⟨U, _, hU⟩ := h.exists_compatible_padic_integral_model 2 h2p
  let W := U.map (rationalPadicIntegerMap 2)
  have h1 : W.a₁ = 1 := by
    apply IsFractionRing.injective (padicIntegerSubring 2) ℚ_[2]
    have he := congrArg WeierstrassCurve.a₁ hU
    simpa only [W, WeierstrassCurve.map, h.normalized_coefficients.1, map_one] using he
  refine ⟨W, hU, (residue_ne_zero_iff_isUnit W.c₄).mp ?_⟩
  have h4 : (4 : ResidueField (padicIntegerSubring 2)) = 0 :=
    (CharP.cast_eq_zero_iff _ 2 _).mpr (by decide)
  have h24 : (24 : ResidueField (padicIntegerSubring 2)) = 0 :=
    (CharP.cast_eq_zero_iff _ 2 _).mpr (by decide)
  have hc : residue (padicIntegerSubring 2) W.c₄ = 1 := by
    simp only [WeierstrassCurve.c₄, WeierstrassCurve.b₂, h1, map_sub, map_pow,
      map_add, map_mul, map_ofNat, map_one,
      h4, h24, one_pow, zero_mul, add_zero, sub_zero]
  rw [hc]
  exact one_ne_zero

/-- The canonical target itself is semistable over ℚ₂. -/
theorem IsVeluTarget.padic_two_good_or_multiplicative (h : P.IsVeluTarget E) :
    (E.map (algebraMap ℚ ℚ_[2])).HasGoodReduction (padicIntegerSubring 2) ∨
      (E.map (algebraMap ℚ ℚ_[2])).HasMultiplicativeReduction (padicIntegerSubring 2) := by
  obtain ⟨W, hW, hc⟩ := h.exists_padic_two_unit_model
  simpa only [hW] using (good_or_multiplicative_of_unit_invariants (K := ℚ_[2]) W (Or.inr hc))

/-- The canonical equation requires no further minimalization at two. -/
theorem IsVeluTarget.padic_two_isMinimal (h : P.IsVeluTarget E) :
    IsMinimal (padicIntegerSubring 2) (E.map (algebraMap ℚ ℚ_[2])) := by
  rcases h.padic_two_good_or_multiplicative with hg | hm
  · exact hg.toIsMinimal
  · exact hm.toIsMinimal

end FreyPackage
