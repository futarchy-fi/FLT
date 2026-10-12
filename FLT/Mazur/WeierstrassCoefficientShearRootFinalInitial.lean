/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRootInitialOriginal
public import FLT.Mazur.WeierstrassDividedFinalInitialComponents

import all FLT.Mazur.WeierstrassCoefficientShearRetainedFiber

/-!
# Independent initial components at the original final indices

Assemble the two independently glued initial components at the final stage,
retaining their signed parameters and their original node labels.
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
  (D : SplitNodeDepth W π depth) (s : ℕ) (hsFinal : s + 1 ≤ n)
  (hstart : 0 < start) (hkFinal : 2 * (start + s + 1) ≤ depth)
local notation "h1" => show 1 ≤ n from by omega
local notation "hk" => show 2 * (start + 1) ≤ depth from by omega
local notation "m" => s
local notation "hm" => show 1 + s ≤ n from by omega
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


local notation "transport" => eqToHom
  (finiteGlobalTensorModel_index_congr hπ data K hm hsFinal (by omega))
local notation "Efinal" => coefficientShearGluedIso hπ data K 0 (s + 1) hsFinal
local notation "p" => coefficientShearGluedStructure hπ data K 0 (s + 1) hsFinal

/-- The independently glued initial pair in the final coefficient model. -/
def coefficientShearRootFinalInitialComponent (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ coefficientShearGlued hπ data K 0 (s + 1) hsFinal :=
  Fin.cases
    (coefficientShearRootInitialFirstComponent
      hπ data K 0 h1 m hm hs hp h3 h4 hr g3 g4 hc a ha)
    (fun _ => coefficientShearRootInitialSecondComponent
      hπ data K 0 h1 m hm hs hp h3 h4 hr g3 g4 hc a ha) i ≫
    (G).hom ≫ transport ≫ (Efinal).inv

/-- Reconstruction keeps each original initial component at the actual final index. -/
@[reassoc] theorem coefficientShearRootFinalInitialComponent_original (i : Fin 2) :
    coefficientShearRootFinalInitialComponent hπ data D s hsFinal hstart hkFinal i ≫
        (Efinal).hom = finalInitialComponent hπ data D s hsFinal hstart hkFinal i := by
  simp only [coefficientShearRootFinalInitialComponent, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [finalInitialComponent]
  fin_cases i
  · exact coefficientShearRootInitialFirstComponent_original_assoc
      hπ data D h1 hstart hk m hm transport
  · exact coefficientShearRootInitialSecondComponent_original_assoc
      hπ data D h1 hstart hk m hm transport

/-- The complete pair preserves the original residue-field structure. -/
@[reassoc] theorem coefficientShearRootFinalInitialComponent_structure (i : Fin 2) :
    coefficientShearRootFinalInitialComponent hπ data D s hsFinal hstart hkFinal i ≫ p =
      ProjectiveLine.toBase K := by
  rw [coefficientShearGluedStructure,
    coefficientShearRootFinalInitialComponent_original_assoc, finalInitialComponent_structure]

variable (hpFinal : 2 * (start + s + 1) < depth)

/-- The initial zero marking retains its original optional initial-node label. -/
@[reassoc] theorem coefficientShearRootFinalInitialComponent_zero_original (i : Fin 2) :
    ProjectiveLine.zero K ≫
        coefficientShearRootFinalInitialComponent hπ data D s hsFinal hstart hkFinal i ≫
        (Efinal).hom =
      finalNodeSection hπ data D s hsFinal hkFinal hpFinal (.inl (.inl ⟨i, hstart⟩)) := by
  rw [coefficientShearRootFinalInitialComponent_original, finalInitialComponent_zero]

/-- The initial infinity marking retains its first ordered retained-node label. -/
@[reassoc] theorem coefficientShearRootFinalInitialComponent_infinity_original (i : Fin 2) :
    ProjectiveLine.infinity K ≫
        coefficientShearRootFinalInitialComponent hπ data D s hsFinal hstart hkFinal i ≫
        (Efinal).hom =
      finalNodeSection hπ data D s hsFinal hkFinal hpFinal (.inl (.inr (0, i))) := by
  rw [coefficientShearRootFinalInitialComponent_original, finalInitialComponent_infinity]

/-- Each independent initial component as a morphism over the residue field. -/
def coefficientShearRootFinalInitialOverComponent (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  Over.homMk (coefficientShearRootFinalInitialComponent hπ data D s hsFinal hstart hkFinal i)
    (coefficientShearRootFinalInitialComponent_structure hπ data D s hsFinal hstart hkFinal i)

end FLT.Mazur.WeierstrassDividedDepth
