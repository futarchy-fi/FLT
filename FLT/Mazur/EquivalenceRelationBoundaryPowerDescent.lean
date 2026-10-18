/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryTestPowerEquations
public import FLT.Mazur.EquivalenceRelationBoundaryFaithful
public import FLT.Mazur.EquivalenceRelationBoundaryUniformOrders

/-!
# Descent of the original boundary equations with unchanged exponents

Faithful chart descent turns matching-rank recovery into an explicit equation
on the full scalar product. These are actual ideal powers, not just radicals.
No recovery or nilpotence assumption on residual products is discharged here.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples AffineScalarBoundaryNilpotence
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] source action restrictedAction boundaryProduct boundaryCoordinate
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (n : ℕ) (o : Fin n) (U : (source p q (Fin n) o).Opens)
  (e : CategoryTheory.EquivalenceRelation p q)
  (hU : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ U = U)
  [IsAffine U.toScheme] [IsNoetherian U.toScheme]
  {R T : Type} [CommRing R] [CommRing T]
  (s : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) U hU))
  (κ : R →+* T)
local notation "tests" => completeAffineOrbitTests e (Fin n) o U hU
local notation "π" => chartBoundaryProduct n o U e hU s κ
local notation "b" => chartBoundaryEndpoint n o U e hU s κ
local instance powerDescentOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance powerDescentOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›

omit [QuasiCompact p] in
/-- The full original product and chart have precisely the same test-power equations. -/
theorem boundaryTestChart_power_iff (k : ℕ) :
    (boundaryTestSheaf s κ tests).comap π ^ k = ⊥ ↔
      boundaryTestIdeal s κ tests ^ k = ⊥ := by
  rw [chartBoundaryProduct_sheaf_power_iff, boundaryTestSheaf_pow_eq_bot_iff]

/-- Matching-rank recovery gives an explicit power equation on the full original product. -/
theorem boundary_product_power_of_rank_recovery :
    ∃ d : ℕ, 0 < d ∧ ∀ k : ℕ,
      IsIso (rankPullbackMap (Over.mk p) b n k) →
        boundaryTestIdeal s κ tests ^ (d * (k + 1)) = ⊥ := by
  obtain ⟨d, hd, h⟩ := boundary_test_power_of_rank_recovery n o U e hU s κ
  exact ⟨d, hd, fun k hk ↦ (boundaryTestChart_power_iff n o U e hU s κ _).mp (h k hk)⟩

/-- Finite matching-rank recovery recovers the entire product at a computed test order. -/
theorem boundary_product_recovery_of_rank_recovery :
    ∃ d : ℕ, 0 < d ∧ ∀ k : ℕ,
      IsIso (rankPullbackMap (Over.mk p) b n k) →
        IsIso (boundaryTestThickeningMap s κ tests (d * (k + 1) - 1)) := by
  obtain ⟨d, hd, h⟩ := boundary_product_power_of_rank_recovery n o U e hU s κ
  refine ⟨d, hd, fun k hk ↦ ?_⟩
  rw [boundaryTestThickeningMap_isIso_iff,
    Nat.sub_add_cancel (Nat.mul_pos hd (Nat.succ_pos k))]
  exact h k hk

end FLT.Mazur.EquivalenceRelationNormalizedFrames
