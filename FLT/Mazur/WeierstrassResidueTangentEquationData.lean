/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveShearNormalForm
public import FLT.Mazur.WeierstrassDilatationResidueDepth

/-!
# Actual residue tangent coefficients for the complete incidence equations

The original residue-root algebra supplies the root equation and the vanishing
scale. Vanishing divided linear coefficients pass through the real residue map.
No local-ring or domain instance is required on the integral tangent algebra.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsLocalRing R] (W : WeierstrassCurve R)
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
local notation "q" => algebraMap R Q

/-- The root of the residue tangent polynomial solves the original coefficient equation. -/
theorem residueTangentEquation_root : r ^ 2 + q W.a₁ * r - q W.a₂ = 0 := by
  simpa only [IsScalarTower.algebraMap_apply R K Q, ResidueField.algebraMap_eq,
    WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂] using nodeTangentRoot_equation V

/-- A coefficient in the original maximal ideal vanishes in the actual residue-root algebra. -/
theorem residueTangentEquation_zero (b : R) (hb : b ∈ maximalIdeal R) : q b = 0 := by
  rw [IsScalarTower.algebraMap_apply R K Q,
    show algebraMap R K b = 0 from (residue_eq_zero_iff b).mpr hb, map_zero]

variable {π : R} (hres : residue R π = 0) (k : ℕ) (hk : 0 < k)
include hres hk in
/-- Every positive original modification scale vanishes over the residue-root algebra. -/
theorem residueTangentEquation_scale : q (π ^ k) = 0 := by
  rw [IsScalarTower.algebraMap_apply R K Q, ResidueField.algebraMap_eq, map_pow, hres,
    zero_pow (by omega), map_zero]

variable (b3 b4 b6 : R) (h3 : b3 ∈ maximalIdeal R) (h4 : b4 ∈ maximalIdeal R)

/-- The complete original initial tensor equation over the actual residue tangent algebra. -/
def residueTangentIncidenceEquiv :
    WeierstrassModificationX.ScalarExtension W (π ^ k) b3 b4 b6 Q ≃ₐ[Q]
      WeierstrassModificationX.FiberCoordinate
        (rootShearCurve (W.map q) r).a₁ (q b6) :=
  WeierstrassModificationX.tensorShearNormalEquiv W (π ^ k) b3 b4 b6 Q r
    (residueTangentEquation_scale W hres k hk)
    (residueTangentEquation_zero W b3 h3) (residueTangentEquation_zero W b4 h4)
    (residueTangentEquation_root W)

/-- The entire retained residue tensor equation is the conic extension with its original u. -/
def residueTangentSuccessiveEquiv :
    WeierstrassSuccessiveX.ScalarExtension W (π ^ k) π b3 b4 b6 Q ≃ₐ[Q]
      WeierstrassSuccessiveX.MiddleExtension (rootShearCurve (W.map q) r) (q b6) :=
  WeierstrassSuccessiveX.tensorShearConicExtensionEquiv W (π ^ k) π b3 b4 b6 Q r
    (residueTangentEquation_scale W hres k hk)
    (by rw [IsScalarTower.algebraMap_apply R K Q, ResidueField.algebraMap_eq, hres, map_zero])
    (residueTangentEquation_zero W b3 h3) (residueTangentEquation_zero W b4 h4)
    (residueTangentEquation_root W)

end FLT.Mazur.WeierstrassDividedDepth
