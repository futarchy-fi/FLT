/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFiniteLineReciprocals
public import FLT.Mazur.PolygonNodeLaurentPoints
public import FLT.Mazur.PolygonScaledReciprocal

/-!
# Tangent-scaled horizontal lines on the original divided tensor algebra

Inverse tangent scaling identifies each punctured horizontal line with its
arithmetic Laurent branch. The formulas retain every original tensor function.
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
local notation "F" => ResidueField R
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "f₁" => residueFiniteNodeLineMap hπ data D j hj hk0 hk 0 (by simp)
local notation "f₂" => residueFiniteNodeLineMap hπ data D j hj hk0 hk
  (-residue R W.a₁) (by simp)

/-- Inverse tangent scaling recovers the entire arithmetic positive branch. -/
theorem residueFiniteFirstLine_scaling :
    (PolygonScaledReciprocal.scaling (a)⁻¹).comp (toLaurentAlg.comp f₁) =
      PolygonNodeLaurentPoints.rightAlgebra := by
  apply AlgHom.ext
  intro z
  apply LaurentPolynomial.invert.injective
  exact AlgHom.congr_fun (residueFiniteFirstLine_reciprocal hπ data D j hj hk0 hk) z

/-- The opposite branch retains its original negative tangent scale. -/
theorem residueFiniteSecondLine_scaling :
    (PolygonScaledReciprocal.scaling (-a)⁻¹).comp (toLaurentAlg.comp f₂) =
      PolygonNodeLaurentPoints.leftAlgebra := by
  apply AlgHom.ext
  intro z
  apply LaurentPolynomial.invert.injective
  exact AlgHom.congr_fun (residueFiniteSecondLine_reciprocal hπ data D j hj hk0 hk) z

local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le (Nat.le_of_succ_le hj)))
local notation "T" => WeierstrassDilatation.ScalarExtension W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) F
local notation "E" => WeierstrassDilatation.residuePolygonEquiv D (start + j)
  hk0 (by omega) (Data.b3 d) (Data.b4 d) (Data.b6 d)
  (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) (by omega)

/-- The positive scaled line retains all original divided functions. -/
theorem residueFiniteFirstLine_scaling_tensor (z : T) :
    PolygonScaledReciprocal.scaling (a)⁻¹
      (toLaurent (residueFiniteLineContraction hπ data D j hj hk0 hk 0 (by simp) z)) =
        PolygonNodeLocalization.rightMap (E z) := by
  have H := AlgHom.congr_fun (residueFiniteFirstLine_scaling hπ data D j hj hk0 hk) (E z)
  simp only [AlgHom.comp_apply, residueFiniteNodeLineMap,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at H
  exact H

/-- The negative scaled line retains all original divided functions. -/
theorem residueFiniteSecondLine_scaling_tensor (z : T) :
    PolygonScaledReciprocal.scaling (-a)⁻¹
      (toLaurent (residueFiniteLineContraction hπ data D j hj hk0 hk
        (-residue R W.a₁) (by simp) z)) = PolygonNodeLocalization.leftMap (E z) := by
  have H := AlgHom.congr_fun (residueFiniteSecondLine_scaling hπ data D j hj hk0 hk) (E z)
  simp only [AlgHom.comp_apply, residueFiniteNodeLineMap,
    AlgEquiv.coe_toAlgHom, AlgEquiv.symm_apply_apply] at H
  exact H

end FLT.Mazur.WeierstrassDividedDepth
