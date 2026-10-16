/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassRetainedFixedEdgeUnit
public import FLT.Mazur.NodalFiberZeroTangentMobiusPuncture

/-!
# Full scheme boundaries of the fixed retained comparison

The outgoing and next incoming boundaries factor through the same Laurent
parameter. These are statements about the whole original edge schemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassModificationX
open PolygonSmoothing
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] (π τ : R) (q : Rˣ) (hq : π * (q : R) = τ)
  (U : (ChartRing π)ˣ)
local notation "B" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (LaurentUnitPoints.evalUnit (R := R) (retainedFixedEdgeUnit π q U))))

/-- The full outgoing branch uses the exact fixed-smoothing edge parameter. -/
@[reassoc] theorem retainedFixedSmoothingChart_outgoing :
    leftBranchOpen R π ≫ retainedFixedSmoothingChart π τ (q : R) hq U =
      B ≫ leftBranchOpen R τ := by
  rw [leftBranchOpen_eq_spec, retainedFixedSmoothingChart, ← Spec.map_comp]
  exact boundary_leftBranchOpen τ
    ((leftLaurentMap π).comp (retainedFixedSmoothingEvaluation π τ (q : R) hq U))
    (retainedFixedEdgeUnit π q U) (retainedFixedSmoothingEvaluation_outgoing π q U τ hq)

variable (α : Rˣ) (V V' : (ChartRing π)ˣ)
  (hV : Units.map (leftLaurentMap π).toMonoidHom V =
    Units.map (retainedPrecedingEvaluation π).toMonoidHom V')
local notation "U₀" => retainedScaledCorrectionUnit π α V
local notation "U₁" => retainedScaledCorrectionUnit π (α * q⁻¹) V'
local notation "B₀" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom
  (LaurentUnitPoints.evalUnit (R := R) (retainedFixedEdgeUnit π q U₀))))

include hV in
/-- The next entire incoming branch has the very same target edge parameter. -/
@[reassoc] theorem retainedFixedSmoothingChart_incoming :
    precedingBranch R π ≫ retainedFixedSmoothingChart π τ (q : R) hq U₁ =
      B₀ ≫ precedingBranch R τ := by
  rw [precedingBranch_eq_spec, retainedFixedSmoothingChart, ← Spec.map_comp]
  have h := boundary_rightBranchOpen τ
    ((precedingLaurentMap R π).comp (retainedFixedSmoothingEvaluation π τ (q : R) hq U₁))
    (retainedFixedEdgeUnit π q U₀)⁻¹
    (retainedFixedSmoothingEvaluation_incoming π q τ hq α V V' hV)
  rw [NodalFiber.unitParameter_inverse, Category.assoc] at h
  exact h

end FLT.Mazur.WeierstrassModificationX
