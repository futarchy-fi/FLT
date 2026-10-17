/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationChartFamilyLifts

/-!
# Boundary-kernel discrepancies for arbitrary chart corrections

An arbitrary family vanishing on every exact chart boundary has discrepancy
vanishing on every entire mixed boundary. This holds before any reduction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
open InvariantBoundary SchemeFiniteGroupQuotient FiniteGroupRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
  InvariantBoundary.boundary MixedFrames.relation jointBoundaryTarget
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {ι : Type} (n : ι → ℕ) (o : ∀ a, Fin (n a))
  (U : ∀ a, (source p q (Fin (n a)) (o a)).Opens)
  (hU : ∀ a σ, (EquivalenceRelationNormalizedFrames.action e (Fin (n a)) (o a) σ).hom ⁻¹ᵁ
    U a = U a)
  (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)

variable [Etale p]

include hr hs in
/-- Exact chart boundary kernels map into exact full mixed boundary kernels. -/
theorem difference_mem_kernel_of_restriction_zero (v : Sections e n o U hU)
    (hv : restriction e n o U hU i v = 0) (a b : ι) :
    difference e n o U hU v a b ∈
      RingHom.ker (mixedChartBoundaryInclusion (o a) (o b) (U a) (U b) i).appTop.hom := by
  apply lift_family_difference_mem_kernel e n o U hU i z r s hr hs
    ⊤ (by simp only [Scheme.Hom.preimage_top]) (fun _ ↦ by simp) 0
    (by simp only [map_zero]) v _ a b
  rw [hv]
  funext a
  exact (map_zero _).symm

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames.ChartFamily
