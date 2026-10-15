/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonArithmeticAffinePoints

/-!
# Reconstructing a compatible point contained in one affine neighborhood

Factor the original stage maps through the affine chart, reconstruct their
coordinate maps, and compose with the chart inclusion into the original target.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PolygonArithmeticStages

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

variable (R : Type) [CommRing R] (π : R) {X : Scheme}
variable (s : baseSystem R π ⟶ (Functor.const ℕ).obj X)
  (U : X.Opens) (hU : IsAffineOpen U)
  (hs : ∀ m, Set.range (s.app m) ⊆ (U : Set X))

/-- The original point at each order, factored through the specified affine chart. -/
def stagePointInAffineChart (m : ℕ) : Spec (.of (Quotient R π m)) ⟶ Spec Γ(X, U) :=
  IsOpenImmersion.lift hU.fromSpec (s.app m) (by
    rw [hU.range_fromSpec]
    exact hs m)

/-- Factoring through the chart retains the actual point in the original scheme. -/
@[reassoc] theorem stagePointInAffineChart_fromSpec (m : ℕ) :
    stagePointInAffineChart R π s U hU hs m ≫ hU.fromSpec = s.app m :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factored chart points satisfy the actual adjacent coefficient equation. -/
@[reassoc] theorem stagePointInAffineChart_compatible (m : ℕ) :
    baseRestriction R π m ≫ stagePointInAffineChart R π s U hU hs (m + 1) =
      stagePointInAffineChart R π s U hU hs m := by
  apply (cancel_mono hU.fromSpec).mp
  rw [Category.assoc, stagePointInAffineChart_fromSpec, stagePointInAffineChart_fromSpec]
  have hn := s.naturality (homOfLE (Nat.le_succ m))
  change (baseSystem R π).map (homOfLE (Nat.le_succ m)) ≫ s.app (m + 1) =
    s.app m ≫ 𝟙 X at hn
  have hb : (baseSystem R π).map (homOfLE (Nat.le_succ m)) = baseRestriction R π m :=
    Functor.ofSequence_map_homOfLE_succ _ m
  rw [hb] at hn
  exact hn.trans (Category.comp_id (s.app m))

variable [IsAdicComplete (ideal R π) R]

/-- The complete point in the original target, reconstructed inside its affine neighborhood. -/
def pointFromAffineStages : Spec (.of R) ⟶ X :=
  affineStagePoint R π Γ(X, U) (stagePointInAffineChart R π s U hU hs)
    (stagePointInAffineChart_compatible R π s U hU hs) ≫ hU.fromSpec

/-- Every finite restriction of the reconstructed point is the specified original map. -/
@[reassoc] theorem baseToIntegral_pointFromAffineStages (m : ℕ) :
    baseToIntegral R π m ≫ pointFromAffineStages R π s U hU hs = s.app m := by
  rw [pointFromAffineStages, ← Category.assoc, baseToIntegral_affineStagePoint,
    stagePointInAffineChart_fromSpec]

/-- The complete point retains the original base map whenever the finite points do. -/
@[reassoc] theorem pointFromAffineStages_toBase
    (p : X ⟶ Spec (.of R))
    (hp : ∀ m, s.app m ≫ p = baseToIntegral R π m) :
    pointFromAffineStages R π s U hU hs ≫ p = 𝟙 _ := by
  apply affinePoint_ext R π (.of R)
  intro m
  rw [← Category.assoc, baseToIntegral_pointFromAffineStages, hp, Category.comp_id]

end FLT.Mazur.PolygonArithmeticStages
