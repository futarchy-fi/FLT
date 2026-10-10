/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteLineBoundary
public import FLT.Mazur.WeierstrassDividedAdjacentBoundaryReciprocals

/-!
# The actual geometric line map through the preceding tensor boundary

The spectrum of the complete boundary algebra map is exactly the original
horizontal line lift followed by the tensor transition.
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
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "e" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "A" => WeierstrassDilatation.Coordinate W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "p" => WeierstrassDilatation.parameterEquiv W (π ^ (start + j))
  (π ^ (start + j)) (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (π * Data.b3 e) (π * Data.b4 e) (π ^ 2 * Data.b6 e) rfl
  (factor3_step hπ d e) (factor4_step hπ d e) (factor6_step hπ d e)
local notation "f" => tensorPreviousMap W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) K
local notation "tx" => WeierstrassDilatation.tensorX W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
local notation "ty" => WeierstrassDilatation.tensorY W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K
variable (r : ResidueField R) (hr : r * (r + residue R W.a₁) = 0)
local notation "L" => residueSuccessiveLineMap D (start + j) hk0 hk
  (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) r hr


local notation "x" => WeierstrassDilatation.x W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 2
local notation "a" => previousBoundaryEquiv hπ d e
local notation "φ" => residueFiniteLineContraction hπ data D j hj hk0 hk r hr

/-- The actual geometric line lift retains the entire parameter-corrected boundary map. -/
theorem residueFiniteLineBoundary_spec :
    residueLineToHorizontal D (start + j) hk0 hk (Data.b3 e) (Data.b4 e)
      (Data.b6 e) (Data.factor3 e) (Data.factor4 e) r hr ≫
        (PrincipalOpenTensor.transitionIso K x u a).hom =
      Spec.map (CommRingCat.ofHom
        (residueFiniteLineBoundaryMap hπ data D j hj hk0 hk r hr).toRingHom) := by
  rw [residueLineToHorizontal_eq_spec]
  exact (lineSpec_comp (PrincipalOpenTensor.transition K x u a).toAlgHom
    (residueLineHorizontalMap D (start + j) hk0 hk (Data.b3 e) (Data.b4 e)
      (Data.b6 e) (Data.factor3 e) (Data.factor4 e) r hr)).symm

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
theorem adjacentConicFirstLine_boundary_spec :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g₁)) ≫
      Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom copen).toRingHom) =
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ρ₁)) ≫
      LNext 0 (by simp) ≫ (B).hom := by
  have H := congrArg (fun q : Q →ₐ[K] K[T;T⁻¹] =>
    Spec.map (CommRingCat.ofHom q.toRingHom))
      (adjacentConicFirstLine_localization hπ data D j hj hk0 hk hjNext hkNext)
  rw [lineSpec_comp, lineSpec_comp] at H
  exact H.trans (congrArg (fun m => Spec.map (CommRingCat.ofHom
    (AlgHom.toRingHom ρ₁)) ≫ m)
      (residueFiniteLineBoundary_spec hπ data D (j + 1) hjNext
        (by omega) hkNext 0 (by simp)).symm)

/-- The opposite conic puncture keeps the original negative reciprocal line transition. -/
theorem adjacentConicSecondLine_boundary_spec :
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom g₂)) ≫
      Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom copen).toRingHom) =
    Spec.map (CommRingCat.ofHom (AlgHom.toRingHom ρ₂)) ≫
      LNext (-residue R W.a₁) (by simp) ≫ (B).hom := by
  have H := congrArg (fun q : Q →ₐ[K] K[T;T⁻¹] =>
    Spec.map (CommRingCat.ofHom q.toRingHom))
      (adjacentConicSecondLine_localization hπ data D j hj hk0 hk hjNext hkNext)
  rw [lineSpec_comp, lineSpec_comp] at H
  exact H.trans (congrArg (fun m => Spec.map (CommRingCat.ofHom
    (AlgHom.toRingHom ρ₂)) ≫ m)
      (residueFiniteLineBoundary_spec hπ data D (j + 1) hjNext
        (by omega) hkNext (-residue R W.a₁) (by simp)).symm)

end FLT.Mazur.WeierstrassDividedDepth
