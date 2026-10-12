/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTerminalComponents
public import FLT.Mazur.WeierstrassCoefficientShearRootTerminalComponents

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Root-zero compatibility of independent terminal components

The independent arbitrary-root gluing recovers the original split-residue
components with both full charts and the original terminal indices.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open scoped TensorProduct
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassDilatation WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
  (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "V" => W.map (residue R)
local notation "hs" => WeierstrassDilatation.residue_scale_eq_zero D (start + (j + 1)) (by omega)
local notation "h3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (divided_linear_mem D (start + (j + 1)) hk
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (divided_linear_mem D (start + (j + 1)) hk
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h6" => Iff.mpr (residue_eq_zero_iff _)
  (divided_constant_mem D (start + (j + 1)) hp (Data.b6 d) (Data.factor6 d))
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "a" => residueTangentUnit D
local notation "ha" => Eq.trans (residueTangentUnit_val D) (Eq.symm (rootShearZero_tangent V))
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "hsPrev" => WeierstrassDilatation.residue_scale_eq_zero D (start + j) hk0
local notation "hπ₀" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "C" => coefficientShearRetainedConic hπ data K 0
  (j + 1) hj ⟨j, Nat.lt_succ_self j⟩ hsPrev hπ₀ h3 h4 hr
local notation "c" => residue R (Data.b6 d)
local notation "E" => conicZeroAffineIso c h6
local notation "P₁" => (E).hom ≫ coefficientConicFirstParameter
  (rootShearCurve V 0).a₁ c hu C
local notation "P₂" => (E).hom ≫ coefficientConicSecondParameter
  (rootShearCurve V 0).a₁ c hu C
local notation "B₁" => coefficientShearTerminalFirstBranch
  hπ data K 0 (j + 1) hj hs h3 h4 h6 hr a ha
local notation "B₂" => coefficientShearTerminalSecondBranch
  hπ data K 0 (j + 1) hj hs h3 h4 h6 hr a ha
local notation "G" => coefficientShearGluedIso hπ data K 0 (j + 1) hj

/-- Root zero recovers the full original first coefficient component. -/
theorem coefficientShearRootTerminalFirstComponent_rootZero :
    coefficientShearRootTerminalFirstComponent
        hπ data K 0 j hj hsPrev hπ₀ h3 h4 h6 hr a ha =
      coefficientShearTerminalFirstComponent hπ data D j hj hk0 hk hp := by
  rfl

/-- Reconstruction retains the actual original first terminal projective line. -/
@[reassoc] theorem coefficientShearRootTerminalFirstComponent_original :
    coefficientShearRootTerminalFirstComponent
        hπ data K 0 j hj hsPrev hπ₀ h3 h4 h6 hr a ha ≫ (G).hom =
      terminalFirstComponent hπ data D j hj hk0 hk hp := by
  rw [coefficientShearRootTerminalFirstComponent_rootZero]
  exact coefficientShearTerminalFirstComponent_original hπ data D j hj hk0 hk hp

/-- Root zero recovers the full original second coefficient component. -/
theorem coefficientShearRootTerminalSecondComponent_rootZero :
    coefficientShearRootTerminalSecondComponent
        hπ data K 0 j hj hsPrev hπ₀ h3 h4 h6 hr a ha =
      coefficientShearTerminalSecondComponent hπ data D j hj hk0 hk hp := by
  rfl

/-- Reconstruction retains the actual original second terminal projective line. -/
@[reassoc] theorem coefficientShearRootTerminalSecondComponent_original :
    coefficientShearRootTerminalSecondComponent
        hπ data K 0 j hj hsPrev hπ₀ h3 h4 h6 hr a ha ≫ (G).hom =
      terminalSecondComponent hπ data D j hj hk0 hk hp := by
  rw [coefficientShearRootTerminalSecondComponent_rootZero]
  exact coefficientShearTerminalSecondComponent_original hπ data D j hj hk0 hk hp

end FLT.Mazur.WeierstrassDividedDepth
