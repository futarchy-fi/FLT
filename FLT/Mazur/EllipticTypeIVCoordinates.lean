/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSingularPointChart
public import FLT.Mazur.EllipticTypeIVResidue

/-!
# Divided coordinates above the additive singular point

Every actual point outside E₀ has coordinates (πx,πy). Negation sends the
divided y-coordinate to -y-a₁x-a₃/π. These are actual affine representatives,
with no assumed component classification.
-/

@[expose] public section

namespace FLT.Mazur

open WeierstrassCurve IsLocalRing

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)

/-- Divided integral coordinates representing an actual generic point. -/
structure TypeIVCoordinates (π : A) (P : (W.map (algebraMap A K)).toProjective.Point) where
  /-- The divided x-coordinate. -/
  x : A
  /-- The divided y-coordinate. -/
  y : A
  nonsingular : (W.map (algebraMap A K)).toAffine.Nonsingular
    ((π * x : A) : K) ((π * y : A) : K)
  represents : P = Affine.Point.toProjective (.some _ _ nonsingular)

/-- Every singularly reducing point admits divided integral coordinates. -/
theorem exists_typeIVCoordinates (π : A) (hgen : maximalIdeal A = Ideal.span {π})
    (h3 : W.a₃ ∈ maximalIdeal A) (h4 : W.a₄ ∈ maximalIdeal A)
    (h6 : W.a₆ ∈ maximalIdeal A)
    (P : (W.map (algebraMap A K)).toProjective.Point) (hP : ¬ SmoothReduction A W P) :
    Nonempty (TypeIVCoordinates A W π P) := by
  obtain ⟨x, y, hn, hx, hy, hp⟩ := exists_singular_integral_affine A W h3 h4 h6 P hP
  obtain ⟨a, ha⟩ := exists_node_coordinate_factor hgen 1 (by simpa using hx)
  obtain ⟨b, hb⟩ := exists_node_coordinate_factor hgen 1 (by simpa using hy)
  simp only [pow_one] at ha hb
  subst x y
  exact ⟨⟨a, b, hn, hp⟩⟩

variable {A W} {π : A} {P : (W.map (algebraMap A K)).toProjective.Point}

/-- The divided coordinates satisfy the original integral equation. -/
theorem TypeIVCoordinates.equation (v : TypeIVCoordinates A W π P) :
    W.toAffine.Equation (π * v.x) (π * v.y) :=
  (W.toAffine.map_equation (IsFractionRing.injective A K) _ _).mp v.nonsingular.1

/-- Negation on divided integral coordinates. -/
noncomputable def TypeIVCoordinates.neg (v : TypeIVCoordinates A W π P)
    (e3 : A) (h3 : W.a₃ = π * e3) : TypeIVCoordinates A W π (-P) := by
  have hy : ((π * (-v.y - W.a₁ * v.x - e3) : A) : K) =
      (W.map (algebraMap A K)).toAffine.negY ((π * v.x : A) : K) ((π * v.y : A) : K) := by
    simp only [Affine.negY, map_a₁, map_a₃, h3, ValuationSubring.algebraMap_apply]
    push_cast
    ring
  refine ⟨v.x, -v.y - W.a₁ * v.x - e3, ?_, ?_⟩
  · rw [hy]
    exact (Affine.nonsingular_neg ..).mpr v.nonsingular
  · conv_lhs => rw [v.represents, ← toProjective_neg, Affine.Point.neg_some]
    apply congrArg Affine.Point.toProjective
    simp only [Affine.Point.some.injEq]
    exact ⟨True.intro, hy.symm⟩

/-- The divided y-coordinate of the inverse has the opposite residual label. -/
theorem TypeIVCoordinates.neg_residue (v : TypeIVCoordinates A W π P)
    (e3 : A) (h3 : W.a₃ = π * e3) (h1 : W.a₁ ∈ maximalIdeal A) :
    residue A (v.neg e3 h3).y = -residue A v.y - residue A e3 := by
  change residue A (-v.y - W.a₁ * v.x - e3) = _
  simp only [map_sub, map_neg, map_mul, (residue_eq_zero_iff _).mpr h1, zero_mul, sub_zero]

end FLT.Mazur
