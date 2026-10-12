/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassNodalResidueTangentDepth
public import FLT.Mazur.WeierstrassCoefficientShearResidueTangentConjugation

/-!
# Canonical roots and units for actual residue-tangent components

The original nodal depth conditions supply a tangent unit. The companion root
and its negative unit are derived in the actual residue algebra, with the
original coefficient involution carrying the companion back to the chosen root.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
local notation "q" => algebraMap R Q

/-- The second root in the actual residue tangent algebra. -/
def residueTangentCompanion : Q := -q W.a₁ - r

/-- Both actual roots have the required original sum. -/
theorem residueTangentCompanion_sum : r + residueTangentCompanion W = -q W.a₁ := by
  unfold residueTangentCompanion
  ring

/-- The companion satisfies the original unsheared tangent equation. -/
theorem residueTangentCompanion_equation :
    residueTangentCompanion W ^ 2 + q W.a₁ * residueTangentCompanion W - q W.a₂ = 0 := by
  unfold residueTangentCompanion
  linear_combination residueTangentEquation_root W

/-- The actual coefficient conjugation exchanges the distinguished root and its companion. -/
theorem residueTangentCompanion_conjugation_root :
    tangentResidueConjugationAlgHom (W := W) r = residueTangentCompanion W := by
  change nodeTangentConjugationHom V r = _
  rw [nodeTangentConjugationHom_root]
  simp only [residueTangentCompanion, IsScalarTower.algebraMap_apply R (ResidueField R) Q,
    ResidueField.algebraMap_eq, WeierstrassCurve.map_a₁]

/-- The companion returns to the chosen root under the same actual coefficient operation. -/
theorem residueTangentCompanion_conjugation :
    tangentResidueConjugationAlgHom (W := W) (residueTangentCompanion W) = r := by
  rw [← residueTangentCompanion_conjugation_root]
  exact nodeTangentConjugationHom_involutive V r

variable {depth : ℕ}
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)

/-- The actual tangent separation unit, constructed from the original c₄ unit condition. -/
def residueTangentComponentUnit : Qˣ := (nodalDepth_tangent_a₁_isUnit h3 h4 hc).unit

/-- Its value is the coefficient of the actual sheared residue equation. -/
theorem residueTangentComponentUnit_val :
    (residueTangentComponentUnit W h3 h4 hc : Q) = (rootShearCurve (W.map q) r).a₁ :=
  (nodalDepth_tangent_a₁_isUnit h3 h4 hc).unit_spec

/-- The companion shear uses the negative of the same unit, including in characteristic two. -/
theorem residueTangentComponentUnit_companion :
    ((-residueTangentComponentUnit W h3 h4 hc : Qˣ) : Q) =
      (rootShearCurve (W.map q) (residueTangentCompanion W)).a₁ := by
  rw [Units.val_neg, residueTangentComponentUnit_val,
    (rootShearCurve_coefficients r).1,
    (rootShearCurve_coefficients (residueTangentCompanion W)).1]
  simp only [WeierstrassCurve.map_a₁, residueTangentCompanion]
  ring

end FLT.Mazur.WeierstrassDividedDepth
