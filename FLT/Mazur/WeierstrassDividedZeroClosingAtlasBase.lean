/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFourthZeroClosingBase

/-!
# Original bases of every depth-zero closing atlas

Transport the original global coefficient projection through the first five
whole-node rounds and the finite diagonal correction. Both full closing
charts retain all arithmetic coefficients.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages PolygonSmoothing WeierstrassModificationX
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
  arithmeticZeroFiniteInitialIso arithmeticInitialFactorRatioChart
  arithmeticZeroFiniteAtlasIso arithmeticZeroFiniteAtlasChart
  simultaneousTwistedArithmeticIso arithmeticLabeledAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {n : ℕ} (data : (i : Fin (n + 1)) → Data W π (1 + i.val))
  (H : ArithmeticAtlasCoefficients data) (m : ℕ) (hj : 1 ≤ n)
  (u : Rˣ) (hu : (data ⟨1, Nat.lt_succ_of_le hj⟩).b6 = π * ↑u)
local notation "Q" => Quotient R π m
local notation "q" => arithmeticZeroDiagonalSourceToBase hπ data H m hj u hu
local notation "τ" => arithmeticInitialMobiusSmoothing W H.a1_unit (π ^ 1) π m
local notation "c₁" => arithmeticZeroFirstAtlasChart hπ data H m hj u hu

/-- The first full retained chart inherits the original global arithmetic base. -/
@[reassoc] theorem arithmeticZeroFirstAtlas_retained_base (b : Bool) :
    c₁ (.retained ⟨0, by omega⟩ b) ≫ q =
      chartStructure Q (arithmeticZeroFirstLastSmoothing hπ data H 0 hj u hu m b) := by
  apply (cancel_epi (arithmeticZeroFirstLastIso hπ data H m 0 hj u hu b).hom).mp
  rw [arithmeticZeroFirstLastIso_base]
  simp only [arithmeticZeroFirstAtlasChart, arithmeticZeroFirstAtlasCorrection,
    Iso.trans_inv, Iso.symm_inv, Category.assoc, Iso.hom_inv_id_assoc]
  rw [arithmeticFourthOuterZeroLast_base, twistedRetainedOrientation_base]

/-- The first atlas retains its entire common terminal with the original global base. -/
@[reassoc] theorem arithmeticZeroFirstAtlas_terminal_base :
    c₁ .terminal ≫ q =
      chartStructure Q (arithmeticFourthTerminalSmoothing hπ data H 0 hj u hu m) := by
  dsimp only [arithmeticZeroFirstAtlasChart, arithmeticZeroFirstAtlasCorrection,
    arithmeticFourthOuterAtlasObject, arithmeticFourthInitialAtlasObject,
    arithmeticFourthAtlasObject]
  rw [Iso.refl_inv]
  erw [Category.id_comp]
  exact arithmeticFourthOuterZeroTerminal_base hπ data H m hj u hu

/-- The second full retained chart retains its original global coefficient base. -/
@[reassoc] theorem arithmeticZeroSecondAtlas_retained_base (b : Bool) :
    arithmeticZeroSecondAtlasChart hπ data H m hj u hu (.retained ⟨0, by omega⟩ b) ≫ q =
      chartStructure Q (arithmeticZeroSecondLastSmoothing hπ data H 0 hj u hu m b) := by
  apply (cancel_epi (arithmeticZeroSecondLastIso hπ data H m 0 hj u hu b).hom).mp
  rw [arithmeticZeroSecondLastIso_base]
  change (arithmeticZeroSecondAtlasCorrection hπ data H m hj u hu (.retained ⟨0, by omega⟩ b)).hom ≫
    _ = _
  rw [← Category.assoc, arithmeticZeroSecondAtlasCorrection_chart]
  exact arithmeticZeroFirstAtlas_retained_base hπ data H m hj u hu b

/-- The second full terminal chart retains its original global coefficient base. -/
@[reassoc] theorem arithmeticZeroSecondAtlas_terminal_base :
    arithmeticZeroSecondAtlasChart hπ data H m hj u hu .terminal ≫ q =
      chartStructure Q (arithmeticZeroSecondTerminalSmoothing hπ data H 0 hj u hu m) := by
  apply (cancel_epi (arithmeticZeroSecondTerminalIso hπ data H m 0 hj u hu).hom).mp
  rw [arithmeticZeroSecondTerminalIso_base]
  change (arithmeticZeroSecondAtlasCorrection hπ data H m hj u hu .terminal).hom ≫ _ = _
  rw [← Category.assoc, arithmeticZeroSecondAtlasCorrection_chart]
  exact arithmeticZeroFirstAtlas_terminal_base hπ data H m hj u hu

/-- The third full retained chart retains its original global coefficient base. -/
@[reassoc] theorem arithmeticZeroThirdAtlas_retained_base (b : Bool) :
    arithmeticZeroThirdAtlasChart hπ data H m hj u hu (.retained ⟨0, by omega⟩ b) ≫ q =
      chartStructure Q (arithmeticZeroThirdLastSmoothing hπ data H 0 hj u hu m b) := by
  apply (cancel_epi (arithmeticZeroThirdLastIso hπ data H m 0 hj u hu b).hom).mp
  rw [arithmeticZeroThirdLastIso_base]
  change (arithmeticZeroThirdAtlasCorrection hπ data H m hj u hu (.retained ⟨0, by omega⟩ b)).hom ≫
    _ = _
  rw [← Category.assoc, arithmeticZeroThirdAtlasCorrection_chart]
  exact arithmeticZeroSecondAtlas_retained_base hπ data H m hj u hu b

/-- The third full terminal chart retains its original global coefficient base. -/
@[reassoc] theorem arithmeticZeroThirdAtlas_terminal_base :
    arithmeticZeroThirdAtlasChart hπ data H m hj u hu .terminal ≫ q =
      chartStructure Q (arithmeticZeroThirdTerminalSmoothing hπ data H 0 hj u hu m) := by
  apply (cancel_epi (arithmeticZeroThirdTerminalIso hπ data H m 0 hj u hu).hom).mp
  rw [arithmeticZeroThirdTerminalIso_base]
  change (arithmeticZeroThirdAtlasCorrection hπ data H m hj u hu .terminal).hom ≫ _ = _
  rw [← Category.assoc, arithmeticZeroThirdAtlasCorrection_chart]
  exact arithmeticZeroSecondAtlas_terminal_base hπ data H m hj u hu

/-- The fourth full retained chart retains its original global coefficient base. -/
@[reassoc] theorem arithmeticZeroFourthAtlas_retained_base (b : Bool) :
    arithmeticZeroFourthAtlasChart hπ data H m hj u hu (.retained ⟨0, by omega⟩ b) ≫ q =
      chartStructure Q (arithmeticZeroFourthLastSmoothing hπ data H 0 hj u hu m b) := by
  apply (cancel_epi (arithmeticZeroFourthLastIso hπ data H m 0 hj u hu b).hom).mp
  rw [arithmeticZeroFourthLastIso_base]
  change (arithmeticZeroFourthAtlasCorrection hπ data H m hj u hu (.retained ⟨0, by omega⟩ b)).hom ≫
    _ = _
  rw [← Category.assoc, arithmeticZeroFourthAtlasCorrection_chart]
  exact arithmeticZeroThirdAtlas_retained_base hπ data H m hj u hu b

/-- The fourth full terminal chart retains its original global coefficient base. -/
@[reassoc] theorem arithmeticZeroFourthAtlas_terminal_base :
    arithmeticZeroFourthAtlasChart hπ data H m hj u hu .terminal ≫ q =
      chartStructure Q (arithmeticZeroFourthTerminalSmoothing hπ data H 0 hj u hu m) := by
  apply (cancel_epi (arithmeticZeroFourthTerminalIso hπ data H m 0 hj u hu).hom).mp
  rw [arithmeticZeroFourthTerminalIso_base]
  change (arithmeticZeroFourthAtlasCorrection hπ data H m hj u hu .terminal).hom ≫ _ = _
  rw [← Category.assoc, arithmeticZeroFourthAtlasCorrection_chart]
  exact arithmeticZeroThirdAtlas_terminal_base hπ data H m hj u hu

/-- The fifth full retained chart retains its original global coefficient base. -/
@[reassoc] theorem arithmeticZeroFifthAtlas_retained_base (b : Bool) :
    arithmeticZeroFifthAtlasChart hπ data H m hj u hu (.retained ⟨0, by omega⟩ b) ≫ q =
      chartStructure Q (arithmeticZeroFifthLastSmoothing hπ data H 0 hj u hu m b) := by
  apply (cancel_epi (arithmeticZeroFifthLastIso hπ data H m 0 hj u hu b).hom).mp
  rw [arithmeticZeroFifthLastIso_base]
  change (arithmeticZeroFifthAtlasCorrection hπ data H m hj u hu (.retained ⟨0, by omega⟩ b)).hom ≫
    _ = _
  rw [← Category.assoc, arithmeticZeroFifthAtlasCorrection_chart]
  exact arithmeticZeroFourthAtlas_retained_base hπ data H m hj u hu b

/-- The fifth full terminal chart retains its original global coefficient base. -/
@[reassoc] theorem arithmeticZeroFifthAtlas_terminal_base :
    arithmeticZeroFifthAtlasChart hπ data H m hj u hu .terminal ≫ q =
      chartStructure Q (arithmeticZeroFifthTerminalSmoothing hπ data H 0 hj u hu m) := by
  apply (cancel_epi (arithmeticZeroFifthTerminalIso hπ data H m 0 hj u hu).hom).mp
  rw [arithmeticZeroFifthTerminalIso_base]
  change (arithmeticZeroFifthAtlasCorrection hπ data H m hj u hu .terminal).hom ≫ _ = _
  rw [← Category.assoc, arithmeticZeroFifthAtlasCorrection_chart]
  exact arithmeticZeroFourthAtlas_terminal_base hπ data H m hj u hu

/-- The finite full retained chart retains its original global coefficient base. -/
@[reassoc] theorem arithmeticZeroFiniteAtlas_retained_base (k : ℕ) (b : Bool) :
    arithmeticZeroFiniteAtlasChart hπ data H k m hj u hu (.retained ⟨0, by omega⟩ b) ≫ q =
      chartStructure Q ((arithmeticZeroFiniteState hπ data H 0 hj u hu k).last m b) := by
  apply (cancel_epi (arithmeticZeroFiniteLastIso hπ data H k m 0 hj u hu b).hom).mp
  rw [arithmeticZeroFiniteLastIso_base]
  change (arithmeticZeroFiniteAtlasCorrection hπ data H k m hj u hu
    (.retained ⟨0, by omega⟩ b)).hom ≫
    _ = _
  rw [← Category.assoc, arithmeticZeroFiniteAtlasCorrection_chart]
  exact arithmeticZeroFifthAtlas_retained_base hπ data H m hj u hu b

/-- The finite full terminal chart retains its original global coefficient base. -/
@[reassoc] theorem arithmeticZeroFiniteAtlas_terminal_base (k : ℕ) :
    arithmeticZeroFiniteAtlasChart hπ data H k m hj u hu .terminal ≫ q =
      chartStructure Q ((arithmeticZeroFiniteState hπ data H 0 hj u hu k).terminal m) := by
  apply (cancel_epi (arithmeticZeroFiniteTerminalIso hπ data H k m 0 hj u hu).hom).mp
  rw [arithmeticZeroFiniteTerminalIso_base]
  change (arithmeticZeroFiniteAtlasCorrection hπ data H k m hj u hu .terminal).hom ≫ _ = _
  rw [← Category.assoc, arithmeticZeroFiniteAtlasCorrection_chart]
  exact arithmeticZeroFifthAtlas_terminal_base hπ data H m hj u hu

end FLT.Mazur.WeierstrassDividedDepth
