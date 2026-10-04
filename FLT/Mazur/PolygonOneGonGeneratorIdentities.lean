/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonCubicElimination
public import FLT.Mazur.OneGonMobiusConductors
public import FLT.Mazur.PuncturedNodeRestrictionComparison

/-!
# Conductor generator identities in the actual localized one-gon ring

The quadratic denominator and both numerators are expressions in the actual
canonical chart coordinates. Faithful punctured restriction proves these
identities in B_s, including the self-incidence term.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.PolygonOneGonCubicCoordinates
open PolygonPinching PolygonNodeAffineCharts PolygonNodePresentation
open PolygonCubicSections PolygonPowerNodeEndpoints LocalizationJointRestriction
open OneGonTransition OneGonCubicElimination
attribute [local instance] MvPolynomial.gradedAlgebra
variable (K : Type u) [Field K] (hn : 0 < 1)
  {C : Over (Spec (.of K))} (p : components K 1 ⟶ C) (q : nodes K 1 ⟶ C)
  (h : IsPushout (toComponents K 1 hn) (toNodes K 1) p q)
  (a : Fin 1 → Kˣ) (x : Spec (.of K)) (i : Fin 1)

/-- An actual interpolation coordinate in the chosen B localization. -/
def coordinate (k : Fin 3) : Localization.Away (oneDenominator K hn p q h a x) :=
  affineCanonicalChartRingMap K 1 hn p q h a
    (oneDenominatorChart K hn p q h a x)
    (oneDenominatorChart_range_subset K hn p q h a x)
    (ProjectiveSpace.coordinate K _ (canonicalIndex.{u} 1)
      ((cubicCoordinateEquiv.{u} 1).symm (.inr ⟨(i, k)⟩)))

local notation "s" => oneDenominator K hn p q h a x
local notation "c" => coordinate K hn p q h a x i
local notation "r" => restriction bPunctureMap s
local notation "g" => algebraMap (puncture K) (Localization.Away (bPunctureMap s))

/-- Clearing the extra Laurent factor produces the cubic parametrization itself. -/
lemma punctured_parametrization :
    let d := g (oneCanonicalDenominator K a i) * g (mobius K : puncture K)
    let z := g (mobius K : puncture K)
    let w := g (algebraMap K (puncture K) (weight K 1 a 3 i))
    IsUnit d ∧ r (c 0) * d = 1 + w * z ^ 3 ∧
      r (c 1) * d = z ∧ r (c 2) * d = z ^ 2 := by
  dsimp only
  refine ⟨(one_canonical_denominator_isUnit K hn p q h a x i).mul
    ((mobius K).isUnit.map g), ?_, ?_, ?_⟩
  · rw [← mul_assoc, show r (c 0) * g (oneCanonicalDenominator K a i) = _ from
      one_interpolation_equation K hn p q h a x i 0, ← map_mul]
    have he : oneInterpolationNumerator K a i 0 * (mobius K : puncture K) =
        1 + algebraMap K (puncture K) (weight K 1 a 3 i) * (mobius K : puncture K) ^ 3 := by
      simp only [oneInterpolationNumerator, ↓reduceIte, add_mul, Units.inv_mul]
      ring
    rw [he, map_add, map_one, map_mul, map_pow]
  · rw [← mul_assoc, show r (c 1) * g (oneCanonicalDenominator K a i) = _ from
      one_interpolation_equation K hn p q h a x i 1]
    simp [oneInterpolationNumerator]
  · rw [← mul_assoc, show r (c 2) * g (oneCanonicalDenominator K a i) = _ from
      one_interpolation_equation K hn p q h a x i 2]
    simp [oneInterpolationNumerator, pow_two]

/-- Both conductor identities hold in B_s, before any additional localization. -/
lemma generator_identities :
    let w := algebraMap K (Localization.Away s) (weight K 1 a 3 i)
    let H := denominator w (c 0) (c 1) (c 2)
    algebraMap (B (R := K)) (Localization.Away s) u * H =
      conductorNumerator w (c 0) (c 1) (c 2) ∧
    algebraMap (B (R := K)) (Localization.Away s) v * H =
      monomialNumerator w (c 0) (c 1) (c 2) := by
  dsimp only
  obtain ⟨hd, h₀, h₁, h₂⟩ := punctured_parametrization K hn p q h a x i
  have hu := congrArg g (conductor_mobius K)
  have hv := congrArg g (monomial_mobius K)
  simp only [map_mul, map_pow, map_sub, map_one] at hu hv
  have hh := OneGonCubicElimination.generator_identities _ _ _ _ _ _ _ _ hd h₀ h₁ h₂ hu hv
  have hw (b : K) : r (algebraMap K (Localization.Away s) b) =
      g (algebraMap K (puncture K) b) := by
    rw [IsScalarTower.algebraMap_apply K (B (R := K)) (Localization.Away s),
      restriction_algebraMap]
    congr 1
  constructor
  · apply PuncturedNodeRestrictionComparison.one_injective s
    simpa only [denominator, conductorNumerator, map_mul, map_pow, map_add, map_sub,
      map_neg, map_ofNat, map_one, restriction_algebraMap, hw] using hh.1
  · apply PuncturedNodeRestrictionComparison.one_injective s
    simpa only [denominator, monomialNumerator, map_mul, map_pow, map_add, map_sub,
      map_neg, map_ofNat, map_one, restriction_algebraMap, hw] using hh.2

end FLT.Mazur.PolygonOneGonCubicCoordinates
