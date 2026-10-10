/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteNodeContractions
public import FLT.Mazur.WeierstrassSuccessiveXResidueMiddleContraction
public import FLT.Mazur.WeierstrassDilatationResidueBoundaryFunctions

/-!
# Horizontal lines over the actual preceding divided node

Transport the original preceding contraction through its parameter equality
and then through its residue normalization. The line parameter stays the
original horizontal coordinate; neither tangent orientation is changed.
-/

@[expose] public noncomputable section
open IsLocalRing Polynomial
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

/-- Restriction to an actual horizontal line after the preceding parameter transport. -/
def finiteLineContraction : A →ₐ[R] K[X] :=
  (AlgHom.restrictScalars R
    (residueSuccessiveLineMap D (start + j) hk0 hk (Data.b3 e) (Data.b4 e)
      (Data.b6 e) (Data.factor3 e) (Data.factor4 e) r hr)).comp
        ((f).comp (AlgEquiv.toAlgHom p))

/-- The same full contraction on the actual preceding residue tensor algebra. -/
def residueFiniteLineContraction : T →ₐ[K] K[X] :=
  AlgHom.liftEquiv R K _ _ (finiteLineContraction hπ data D j hj hk0 hk r hr)

/-- The tensor horizontal coordinate remains the original line parameter. -/
theorem residueFiniteLineContraction_x :
    residueFiniteLineContraction hπ data D j hj hk0 hk r hr tx = X := by
  change (1 : K) • L (f (p _)) = _
  rw [one_smul]
  rw [WeierstrassDilatation.parameterEquiv_x]
  exact residueSuccessiveLine_previous_x D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) r hr

/-- The tensor vertical coordinate retains the specified original tangent slope. -/
theorem residueFiniteLineContraction_y :
    residueFiniteLineContraction hπ data D j hj hk0 hk r hr ty = X * C r := by
  change (1 : K) • L (f (p _)) = _
  rw [one_smul]
  rw [WeierstrassDilatation.parameterEquiv_y]
  exact residueSuccessiveLine_previous_y D (start + j) hk0 hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) r hr

local notation "E" => WeierstrassDilatation.residuePolygonEquiv D (start + j)
  hk0 (by omega) (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (by omega)
local notation "φ" => residueFiniteLineContraction hπ data D j hj hk0 hk r hr
local notation "a" => WeierstrassDilatation.residueTangentUnit D

/-- The actual horizontal line, expressed on the preceding oriented node algebra. -/
def residueFiniteNodeLineMap : PolygonNodeEqualizer.A (R := K) →ₐ[K] K[X] :=
  (φ).comp (AlgEquiv.toAlgHom (AlgEquiv.symm E))

/-- The first node coordinate is the original vertical coordinate on the line. -/
theorem residueFiniteNodeLineMap_x :
    residueFiniteNodeLineMap hπ data D j hj hk0 hk r hr PolygonNodeLocalization.x =
      X * C r := by
  rw [← WeierstrassDilatation.residuePolygonEquiv_y D (start + j)
    hk0 (by omega) (Data.b3 d) (Data.b4 d) (Data.b6 d)
    (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (by omega)]
  change φ ((E).symm ((E) ty)) = _
  rw [AlgEquiv.symm_apply_apply, residueFiniteLineContraction_y]

/-- The second node coordinate is the other original tangent factor. -/
theorem residueFiniteNodeLineMap_y :
    residueFiniteNodeLineMap hπ data D j hj hk0 hk r hr PolygonNodeLocalization.y =
      X * C (r + residue R W.a₁) := by
  have H : (E) (ty + algebraMap K T (↑a : K) * tx) = PolygonNodeLocalization.y := by
    rw [map_add, map_mul, AlgEquiv.commutes,
      WeierstrassDilatation.residuePolygonEquiv_y,
      WeierstrassDilatation.residuePolygonEquiv_x,
      ← mul_assoc, ← map_mul, Units.mul_inv, map_one, one_mul]
    ring
  rw [← H]
  change φ ((E).symm ((E) (ty + algebraMap K T (↑a : K) * tx))) = _
  rw [AlgEquiv.symm_apply_apply, map_add, map_mul, AlgHom.commutes,
    residueFiniteLineContraction_y, residueFiniteLineContraction_x,
    WeierstrassDilatation.residueTangentUnit_val]
  change X * C r + C (residue R W.a₁) * X = _
  rw [map_add]
  ring

end FLT.Mazur.WeierstrassDividedDepth
