/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCharacterCoordinates
public import FLT.GroupScheme.RaynaudTowerAction

/-!
# Actual point evaluations in the original closure

The coordinate functions are equivariant by construction. Their transport
through the specified closure equivalence retains the original automorphism.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open RaynaudParameters

variable {R K L Ω : Type} [CommRing R] [Field K] [Field L] [Field Ω]
  [Algebra R L] [PerfectField L] [Algebra K L] [Algebra K Ω] [IsAlgClosure K Ω]
  (X : FF R L) (e : L →ₐ[K] Ω)

/-- Actual integral-coordinate evaluation in the prescribed original closure. -/
def FF.towerValue (c : X.CoordinateRing) (x : X.Points) : Ω :=
  towerClosureEquiv e (X.characterCoordinates c x)

/-- Actual evaluation intertwines original automorphisms fixing the tower. -/
theorem FF.towerValue_smul (c : X.CoordinateRing) (x : X.Points)
    (σ : Ω ≃ₐ[K] Ω) (hσ : ∀ a, σ (e a) = e a) :
    X.towerValue e c (towerAutomorphism e σ hσ • x) = σ (X.towerValue e c x) := by
  unfold FF.towerValue
  rw [(X.characterCoordinates c).map_smul]
  exact towerAutomorphism_apply e σ hσ _

/-- The transported coefficient map is the prescribed fraction-field embedding. -/
theorem FF.towerValue_algebraMap (a : R) (x : X.Points) :
    X.towerValue e (algebraMap R X.CoordinateRing a) x = e (algebraMap R L a) := by
  unfold FF.towerValue
  rw [X.characterCoordinates.commutes]
  change towerClosureEquiv e (algebraMap R (AlgebraicClosure L) a) = _
  rw [IsScalarTower.algebraMap_apply R L (AlgebraicClosure L), towerClosureEquiv_algebraMap]

end ThreeAdicPlan
