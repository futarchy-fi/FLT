/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteLineBoundaryGeometry
public import FLT.Mazur.WeierstrassDividedConicBoundaryAllDepths

/-!
# Ordered geometric boundary maps at every preceding depth

The ordered punctures keep the full horizontal tensor transition, including
the initial conic at preceding depth zero.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial AlgebraicGeometry CategoryTheory
open scoped TensorProduct LaurentPolynomial
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))

variable (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
local notation "fData" => data (Fin.mk (j + 2) (Nat.lt_succ_of_le hjNext))
local notation "W₀" => W.map (residue R)
local notation "c" => residue R (Data.b6 e)
local notation "ha" => D.a₁_unit.map (residue R)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D (start + j + 1) (by omega)
    (Data.b6 e) (Data.factor6 e))
local notation "g₁" => conicBoundaryFirst W₀ c ha hc
local notation "g₂" => conicBoundarySecond W₀ c ha hc
local notation "copen" => residueDividedConicOpenEquiv D (start + j) hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e)
local notation "xNext" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "uNext" => coord W (π ^ (start + (j + 1))) π
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) 2
local notation "B" => PrincipalOpenTensor.transitionIso K xNext uNext
  (previousBoundaryEquiv hπ e fData)
local notation "LNext" => residueLineToHorizontal D (start + (j + 1)) (by omega) hkNext
  (Data.b3 fData) (Data.b4 fData) (Data.b6 fData) (Data.factor3 fData) (Data.factor4 fData)
local notation "Q" => ResidueDividedOpen (W := W) (π := π) (start + j)
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "ρ₁" => PolygonScaledReciprocal.reciprocal (tangent)⁻¹
local notation "ρ₂" => PolygonScaledReciprocal.reciprocal (-tangent)⁻¹

/-- The first conic puncture is the original next line lift through the actual tensor boundary. -/
theorem adjacentConicFirstLine_boundary_spec_anyDepth :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g₁)) ≫
      Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom copen).toRingHom) =
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ρ₁)) ≫
      LNext 0 (by simp) ≫ (B).hom := by
  have H := congrArg (fun q : Q →ₐ[K] K[T;T⁻¹] =>
    Spec.map (CommRingCat.ofHom q.toRingHom))
      (adjacentConicFirstLine_localization_anyDepth hπ data D j hj hk hjNext hkNext)
  rw [lineSpec_comp, lineSpec_comp] at H
  exact H.trans (congrArg (fun m => Spec.map (CommRingCat.ofHom
    (AlgHom.toRingHom ρ₁)) ≫ m)
      (residueFiniteLineBoundary_spec hπ data D (j + 1) hjNext
        (by omega) hkNext 0 (by simp)).symm)

/-- The opposite conic puncture keeps the original negative reciprocal line transition. -/
theorem adjacentConicSecondLine_boundary_spec_anyDepth :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g₂)) ≫
      Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom copen).toRingHom) =
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ρ₂)) ≫
      LNext (-residue R W.a₁) (by simp) ≫ (B).hom := by
  have H := congrArg (fun q : Q →ₐ[K] K[T;T⁻¹] =>
    Spec.map (CommRingCat.ofHom q.toRingHom))
      (adjacentConicSecondLine_localization_anyDepth hπ data D j hj hk hjNext hkNext)
  rw [lineSpec_comp, lineSpec_comp] at H
  exact H.trans (congrArg (fun m => Spec.map (CommRingCat.ofHom
    (AlgHom.toRingHom ρ₂)) ≫ m)
      (residueFiniteLineBoundary_spec hπ data D (j + 1) hjNext
        (by omega) hkNext (-residue R W.a₁) (by simp)).symm)

end FLT.Mazur.WeierstrassDividedDepth
