/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearOriginalInitialComponents
public import FLT.Mazur.WeierstrassCoefficientShearRootInitialComponents

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Root-zero compatibility of independent initial projective components

The arbitrary-root construction recovers the original initial projective
components with their signed reciprocal parameters and original indices.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
  (m : ℕ) (hm : 1 + m ≤ n)
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "V" => W.map (residue R)
local notation "U" => rootShearCurve V 0
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega) (Data.b6 d) (Data.factor6 d))
local notation "hs" => WeierstrassDilatation.residue_scale_eq_zero D start hstart
local notation "hp" => Iff.mpr (residue_eq_zero_iff π)
  (D.maximalIdeal_eq ▸ Ideal.mem_span_singleton_self π)
local notation "g3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (WeierstrassDilatation.divided_linear_mem
    D start (by omega) (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "g4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (WeierstrassDilatation.divided_linear_mem
    D start (by omega) (Data.b3 d) (Data.b4 d) (Data.factor3 d) (Data.factor4 d)))
local notation "h3" => Iff.mpr (residue_eq_zero_iff _)
  (And.left (WeierstrassDilatation.divided_linear_mem
    D (start + 1) hk (Data.b3 e) (Data.b4 e) (Data.factor3 e) (Data.factor4 e)))
local notation "h4" => Iff.mpr (residue_eq_zero_iff _)
  (And.right (WeierstrassDilatation.divided_linear_mem
    D (start + 1) hk (Data.b3 e) (Data.b4 e) (Data.factor3 e) (Data.factor4 e)))
local notation "hr" => show (0 : K) ^ 2 + algebraMap R K W.a₁ * 0 -
    algebraMap R K W.a₂ = 0 from by
  rw [zero_pow (by decide : 2 ≠ 0), mul_zero, zero_add, zero_sub, neg_eq_zero]
  exact (residue_eq_zero_iff _).mpr D.a₂_mem
local notation "a" => WeierstrassDilatation.residueTangentUnit D
local notation "ha" => Eq.trans (WeierstrassDilatation.residueTangentUnit_val D)
  (Eq.symm (rootShearZero_tangent V))
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)
local notation "conic" => coefficientShearInitialConic hπ data K 0 (1 + m) hm hs g3 g4 hr
local notation "E" => conicZeroAffineIso c hc
local notation "F₁" => (E).hom ≫ coefficientConicFirstParameter (U).a₁ c hu conic
local notation "F₂" => (E).hom ≫ coefficientConicSecondParameter (U).a₁ c hu conic
local notation "line" => coefficientShearRetainedLine hπ data K 0 (1 + m) hm
  (Fin.mk 0 (by omega)) hs hp h3 h4 hr
local notation "L₁" => line 0 (middle_first_root U)
local notation "L₂" => line (-(U).a₁) (middle_second_root U)
local notation "G" => coefficientShearGluedIso hπ data K 0 (1 + m) hm


/-- Root zero recovers the whole original first initial coefficient component. -/
theorem coefficientShearRootInitialFirstComponent_rootZero :
    coefficientShearRootInitialFirstComponent
        hπ data K 0 h1 m hm hs hp h3 h4 hr g3 g4 hc a ha =
      coefficientShearInitialFirstComponent hπ data D h1 hstart hk m hm := by
  rfl

/-- Reconstruction preserves the original first full initial component. -/
@[reassoc] theorem coefficientShearRootInitialFirstComponent_original :
    coefficientShearRootInitialFirstComponent
        hπ data K 0 h1 m hm hs hp h3 h4 hr g3 g4 hc a ha ≫ (G).hom =
      initialGlobalFirstComponent hπ data D h1 hstart hk m hm := by
  rw [coefficientShearRootInitialFirstComponent_rootZero]
  exact coefficientShearInitialFirstComponent_original hπ data D h1 hstart hk m hm

/-- Root zero recovers the whole original second initial coefficient component. -/
theorem coefficientShearRootInitialSecondComponent_rootZero :
    coefficientShearRootInitialSecondComponent
        hπ data K 0 h1 m hm hs hp h3 h4 hr g3 g4 hc a ha =
      coefficientShearInitialSecondComponent hπ data D h1 hstart hk m hm := by
  rfl

/-- Reconstruction preserves the original second full initial component. -/
@[reassoc] theorem coefficientShearRootInitialSecondComponent_original :
    coefficientShearRootInitialSecondComponent
        hπ data K 0 h1 m hm hs hp h3 h4 hr g3 g4 hc a ha ≫ (G).hom =
      initialGlobalSecondComponent hπ data D h1 hstart hk m hm := by
  rw [coefficientShearRootInitialSecondComponent_rootZero]
  exact coefficientShearInitialSecondComponent_original hπ data D h1 hstart hk m hm

end FLT.Mazur.WeierstrassDividedDepth
