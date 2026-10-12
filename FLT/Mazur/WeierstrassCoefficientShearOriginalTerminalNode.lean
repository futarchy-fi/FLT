/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearTerminalNode
import all FLT.Mazur.WeierstrassCoefficientShearTerminalNode
public import FLT.Mazur.WeierstrassConicCoefficientTransport
public import FLT.Mazur.WeierstrassDilatationResidueBoundaryFunctions
public import FLT.Mazur.WeierstrassDividedTerminalNodeIncidence

/-!
# The actual sheared terminal node reconstructs the original node chart

Compare both original tensor generators before applying spectrum. The whole
node chart and its branches therefore retain the original terminal marking.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j) ≤ depth)
  (hp : 2 * (start + j) < depth)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk j (Nat.lt_succ_of_le hj))
local notation "V" => W.map (residue R)
local notation "hs" => WeierstrassDilatation.residue_scale_eq_zero D (start + j) hk0
local notation "h3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (divided_linear_mem D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (divided_linear_mem D (start + j) hk
    (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h6" => Iff.mpr (residue_eq_zero_iff _)
  (divided_constant_mem D (start + j) hp (Data.b6 d) (Data.factor6 d))
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "a" => residueTangentUnit D
local notation "ha" => Eq.trans (residueTangentUnit_val D) (Eq.symm (rootShearZero_tangent V))
local notation "F" => tensorShearNodeEquiv W (π ^ (start + j))
  (Data.b3 d) (Data.b4 d) (Data.b6 d) K 0 hs h3 h4 h6 hr a ha
local notation "N" => coefficientShearTerminalNode hπ data K 0 j hj hs h3 h4 h6 hr a ha
local notation "G" => coefficientShearGluedIso hπ data K 0 j hj
local notation "original" => residueNodeEquiv D (start + j) hk0 hk
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d) (Data.factor6 d) hp

omit [IsBezout R] in
/-- Root-zero normalization preserves every function of the original terminal tensor node. -/
theorem tensorShearNodeEquiv_original : F = original := by
  apply AlgEquiv.coe_toAlgHom_injective
  apply Algebra.TensorProduct.ext_ring
  apply WeierstrassDilatation.hom_ext
  · change F ((1 : K) ⊗ₜ[R] WeierstrassDilatation.x W (π ^ (start + j))
        (Data.b3 d) (Data.b4 d) (Data.b6 d)) = _
    rw [tensorShearNodeEquiv_x]
    exact (residueNodeEquiv_x D (start + j) hk0 hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
      (Data.factor6 d) hp).symm
  · change F ((1 : K) ⊗ₜ[R] WeierstrassDilatation.y W (π ^ (start + j))
        (Data.b3 d) (Data.b4 d) (Data.b6 d)) = _
    rw [tensorShearNodeEquiv_y, map_zero, zero_mul, add_zero]
    exact (residueNodeEquiv_y D (start + j) hk0 hk
      (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
      (Data.factor6 d) hp).symm

/-- Reconstruction recovers the whole original terminal node chart, including its origin. -/
@[reassoc] theorem coefficientShearTerminalNode_original :
    N ≫ (G).hom = terminalNodeChart hπ data D j hj hk0 hk hp := by
  rw [coefficientShearTerminalNode_reconstruction, globalDividedCoefficientShearChart,
    terminalNodeChart, ← Category.assoc]
  apply congrArg (· ≫ globalDividedTensorChart hπ data K j hj)
  change Spec.map _ ≫ Spec.map _ = Spec.map _
  rw [← Spec.map_comp]
  have H := congrArg (fun e => e.trans NodalFiber.polygonNodeEquiv)
    (tensorShearNodeEquiv_original data D j hj hk0 hk hp)
  exact congrArg (fun e => Spec.map (CommRingCat.ofHom (AlgEquiv.toAlgHom e).toRingHom)) H

/-- Both independently constructed branches retain the actual original terminal node chart. -/
@[reassoc] theorem coefficientShearTerminalFirstBranch_original :
    coefficientShearTerminalFirstBranch hπ data K 0 j hj hs h3 h4 h6 hr a ha ≫ (G).hom =
      PolygonCyclicAtlas.firstBranch K ≫ terminalNodeChart hπ data D j hj hk0 hk hp := by
  rw [coefficientShearTerminalFirstBranch, Category.assoc, coefficientShearTerminalNode_original]

/-- The opposite branch retains its original order in the terminal node normalization. -/
@[reassoc] theorem coefficientShearTerminalSecondBranch_original :
    coefficientShearTerminalSecondBranch hπ data K 0 j hj hs h3 h4 h6 hr a ha ≫ (G).hom =
      PolygonCyclicAtlas.secondBranch K ≫ terminalNodeChart hπ data D j hj hk0 hk hp := by
  rw [coefficientShearTerminalSecondBranch, Category.assoc, coefficientShearTerminalNode_original]

end FLT.Mazur.WeierstrassDividedDepth
