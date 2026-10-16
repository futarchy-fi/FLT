/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationChartFamilyCorrections
public import FLT.Mazur.FinitePowerEqualizer

/-!
# Compatible power multiples on finite families of normalized charts

Finitely many torsion discrepancies have a common annihilating exponent.
Multiplication constructs a genuinely compatible chart family, keeping the
full mixed relations and the original nonreduced coefficient rings.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
open SchemeFiniteGroupQuotient FiniteGroupRestriction InvariantSectionObstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  InvariantBoundary.boundary MixedFrames.relation jointBoundaryTarget
variable {D A B : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {ι : Type} (n : ι → ℕ) (o : ∀ a, Fin (n a))
  (U : ∀ a, (source p q (Fin (n a)) (o a)).Opens)
  (hU : ∀ a σ, (action e (Fin (n a)) (o a) σ).hom ⁻¹ᵁ U a = U a)

variable [Finite ι]

/-- A compatible scalar with power-torsion discrepancies constructs one compatible multiple. -/
theorem exists_compatible_power_mul (r v : Sections e n o U hU)
    (hr : ∀ a b, (mixedChartFirst (o a) (o b) (U a) (U b)).appTop (r a).val =
      (mixedChartSecond (o a) (o b) (U a) (U b)).appTop (r b).val)
    (hv : ∀ a b, ∃ N : ℕ,
      ((mixedChartFirst (o a) (o b) (U a) (U b)).appTop (r a).val) ^ N *
        difference e n o U hU v a b = 0) :
    ∃ N : ℕ, ∀ a b,
      (mixedChartFirst (o a) (o b) (U a) (U b)).appTop ((r a ^ N * v a).val) =
        (mixedChartSecond (o a) (o b) (U a) (U b)).appTop ((r b ^ N * v b).val) := by
  obtain ⟨N, hN⟩ := FinitePowerEqualizer.exists_uniform_power
    (fun ab : ι × ι ↦ (mixedChartFirst (o ab.1) (o ab.2) (U ab.1) (U ab.2)).appTop
      (r ab.1).val) (fun ab : ι × ι ↦ difference e n o U hU v ab.1 ab.2)
    (fun ab ↦ hv ab.1 ab.2)
  refine ⟨N, fun a b ↦ ?_⟩
  have he := hN (a, b)
  rw [difference_apply, mul_sub, sub_eq_zero] at he
  change (mixedChartFirst (o a) (o b) (U a) (U b)).appTop
    ((r a).val ^ N * (v a).val) =
      (mixedChartSecond (o a) (o b) (U a) (U b)).appTop ((r b).val ^ N * (v b).val)
  simpa only [map_mul, map_pow, ← hr a b] using he

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
