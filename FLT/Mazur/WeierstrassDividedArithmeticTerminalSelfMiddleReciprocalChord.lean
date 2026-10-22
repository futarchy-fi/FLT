/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfReciprocal
public import FLT.Mazur.WeierstrassDividedMiddleReciprocalChordCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfMiddleTangent

/-!
# Actual arithmetic terminal reciprocal chord outputs at middle depth

Keep both original terminal coordinates and construct the output in the
unchanged smooth model. At exact middle depth the whole reciprocal chord denominator
open is covered, with no puncture assumption. The quotient output preserves
nilpotents and the original coefficient morphisms.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassDilatation
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n)
local notation "idx" => (1 : Fin (j + 3))
local notation "d" => data ⟨j, Nat.lt_succ_of_le hj⟩
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj idx
local notation "fa" => (O).ι ≫ chart idx ≫ s
local notation "input" => arithmeticTerminalSelfReciprocalFormulaInput hπ data m j hj
local notation "al" => dividedPairLeft W (π ^ (0 + j)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + j)) (d).b3 (d).b4 (d).b6
local notation "V" => suppliedReciprocalChordDomain d al ar

/-- The actual reciprocal chord output domain in the full arithmetic terminal self-product. -/
def arithmeticTerminalSelfReciprocalChordOpen : (pullback fa fa).Opens := input ⁻¹ᵁ V

local notation "D" => arithmeticTerminalSelfReciprocalChordOpen hπ data m j hj

/-- The constructed original reciprocal chord output lifts to the entire supplied smooth model. -/
def arithmeticTerminalSelfReciprocalChordAddition : (D).toScheme ⟶ (U).toScheme :=
  (input ∣_ V) ≫ suppliedReciprocalChordResolvedAddition d al ar hπ data j hj

local notation "add" => arithmeticTerminalSelfReciprocalChordAddition hπ data m j hj

/-- The entire reciprocal chord output preserves the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalChordAddition_structure :
    add ≫ t = (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfReciprocalChordAddition, Category.assoc,
    suppliedReciprocalChordResolvedAddition_structure, morphismRestrict_ι_assoc,
    arithmeticTerminalSelfFormulaInput_structure]
  rfl

/-- The same output preserves the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalChordAddition_structure_snd :
    add ≫ t = (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfReciprocalChordAddition_structure, pullback.condition_assoc]

/-- The output retains its full original reciprocal chord contraction. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalChordAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ V) ≫ suppliedReciprocalChordOriginalSmooth d al ar ≫
        (WeierstrassIntegralChart.integralSmoothOpen W).ι := by
  rw [arithmeticTerminalSelfReciprocalChordAddition, Category.assoc,
    suppliedReciprocalChordResolvedAddition_contraction]

/-- The reciprocal chord output lifts over the original quotient, retaining its nilpotents. -/
def arithmeticTerminalSelfReciprocalChordQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst fa fa ≫ fa) add (by
    simpa only [Category.assoc] using
      (arithmeticTerminalSelfReciprocalChordAddition_structure hπ data m j hj).symm)

/-- The quotient projection preserves the entire original coefficient morphism. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalChordQuotientOutput_base :
    arithmeticTerminalSelfReciprocalChordQuotientOutput hπ data m j hj ≫ pullback.fst q t =
      (D).ι ≫ pullback.fst fa fa ≫ fa := by
  simp only [arithmeticTerminalSelfReciprocalChordQuotientOutput, pullback.lift_fst]

/-- The integral projection recovers the whole constructed smooth output. -/
@[reassoc] theorem arithmeticTerminalSelfReciprocalChordQuotientOutput_integral :
    arithmeticTerminalSelfReciprocalChordQuotientOutput hπ data m j hj ≫ pullback.snd q t =
      add := by
  simp only [arithmeticTerminalSelfReciprocalChordQuotientOutput, pullback.lift_snd]

variable [IsLocalRing R] {depth : ℕ} (node : SplitNodeDepth W π depth)
local notation "den" => dividedTangentDenominator W (π ^ (0 + j)) (d).b3 (d).b4 (d).b6 al ar

include node in
/-- Every middle-depth arithmetic pair with vanishing tangent denominator is covered. -/
theorem arithmeticTerminalSelfReciprocalChordOpen_middle_mem
    (hj0 : 0 < j) (hm : 2 * j = depth) (p : (pullback fa fa : Scheme))
    (hd : den ∈ (input p).asIdeal) : p ∈ D := by
  exact suppliedReciprocalChordDomain_middle_mem node d al ar
    (by change 0 < 0 + j; omega) (by change 2 * (0 + j) = depth; omega)
    (input p) (arithmeticTerminalSelfFormulaInput_parameter_mem hπ data m j hj p) hd

include node in
/-- The two genuine output domains cover the whole middle-depth terminal self-product. -/
theorem arithmeticTerminalSelf_middle_cover
    (hj0 : 0 < j) (hm : 2 * j = depth) (p : (pullback fa fa : Scheme)) :
    p ∈ arithmeticTerminalSelfSmoothTangentOpen hπ data m j hj ∨ p ∈ D := by
  exact middleTangentReciprocalChord_cover node d al ar
    (by change 0 < 0 + j; omega) (by change 2 * (0 + j) = depth; omega)
    (input p) (arithmeticTerminalSelfFormulaInput_parameter_mem hπ data m j hj p)

end FLT.Mazur.WeierstrassDividedDepth
