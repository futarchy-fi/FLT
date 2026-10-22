/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfReciprocal
public import FLT.Mazur.WeierstrassDividedMiddleTangentCoverage

/-!
# Actual arithmetic terminal tangent outputs at middle depth

Keep both original terminal coordinates and construct the output in the
unchanged smooth model. At exact middle depth the whole tangent denominator
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
local notation "V" => suppliedSmoothTangentDomain d al ar

/-- The actual tangent output domain in the full arithmetic terminal self-product. -/
def arithmeticTerminalSelfSmoothTangentOpen : (pullback fa fa).Opens := input ⁻¹ᵁ V

local notation "D" => arithmeticTerminalSelfSmoothTangentOpen hπ data m j hj

/-- The constructed original tangent output lifts to the entire supplied smooth model. -/
def arithmeticTerminalSelfSmoothTangentAddition : (D).toScheme ⟶ (U).toScheme :=
  (input ∣_ V) ≫ suppliedSmoothTangentResolvedAddition d al ar hπ data j hj

local notation "add" => arithmeticTerminalSelfSmoothTangentAddition hπ data m j hj

/-- The entire tangent output preserves the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalSelfSmoothTangentAddition_structure :
    add ≫ t = (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfSmoothTangentAddition, Category.assoc,
    suppliedSmoothTangentResolvedAddition_structure, morphismRestrict_ι_assoc,
    arithmeticTerminalSelfFormulaInput_structure]
  rfl

/-- The same output preserves the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticTerminalSelfSmoothTangentAddition_structure_snd :
    add ≫ t = (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticTerminalSelfSmoothTangentAddition_structure, pullback.condition_assoc]

/-- The output retains its full original tangent contraction. -/
@[reassoc] theorem arithmeticTerminalSelfSmoothTangentAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ V) ≫ suppliedSmoothTangentOriginalSmooth d al ar ≫
        (WeierstrassIntegralChart.integralSmoothOpen W).ι := by
  rw [arithmeticTerminalSelfSmoothTangentAddition, Category.assoc,
    suppliedSmoothTangentResolvedAddition_contraction]

/-- The actual tangent output lifts over the original quotient, retaining its nilpotents. -/
def arithmeticTerminalSelfSmoothTangentQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst fa fa ≫ fa) add (by
    simpa only [Category.assoc] using
      (arithmeticTerminalSelfSmoothTangentAddition_structure hπ data m j hj).symm)

/-- The quotient projection preserves the entire original coefficient morphism. -/
@[reassoc] theorem arithmeticTerminalSelfSmoothTangentQuotientOutput_base :
    arithmeticTerminalSelfSmoothTangentQuotientOutput hπ data m j hj ≫ pullback.fst q t =
      (D).ι ≫ pullback.fst fa fa ≫ fa := by
  simp only [arithmeticTerminalSelfSmoothTangentQuotientOutput, pullback.lift_fst]

/-- The integral projection recovers the whole constructed smooth output. -/
@[reassoc] theorem arithmeticTerminalSelfSmoothTangentQuotientOutput_integral :
    arithmeticTerminalSelfSmoothTangentQuotientOutput hπ data m j hj ≫ pullback.snd q t =
      add := by
  simp only [arithmeticTerminalSelfSmoothTangentQuotientOutput, pullback.lift_snd]

variable [IsLocalRing R] {depth : ℕ} (node : SplitNodeDepth W π depth)
local notation "den" => dividedTangentDenominator W (π ^ (0 + j)) (d).b3 (d).b4 (d).b6 al ar

include node in
/-- Every full middle-depth arithmetic pair with invertible tangent denominator is covered. -/
theorem arithmeticTerminalSelfSmoothTangentOpen_middle_mem
    (hj0 : 0 < j) (hm : 2 * j = depth) (p : (pullback fa fa : Scheme))
    (hd : den ∉ (input p).asIdeal) : p ∈ D := by
  exact suppliedSmoothTangentDomain_middle_mem node d al ar
    (by change 0 < 0 + j; omega) (by change 2 * (0 + j) = depth; omega)
    (input p) (arithmeticTerminalSelfFormulaInput_parameter_mem hπ data m j hj p) hd

end FLT.Mazur.WeierstrassDividedDepth
