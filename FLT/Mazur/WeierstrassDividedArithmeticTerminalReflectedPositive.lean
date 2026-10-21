/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticMixedCoverage
public import FLT.Mazur.WeierstrassDividedRetainedTerminalReflected

/-!
# Arithmetic reflected outputs with the full terminal factor

The original terminal input may keep its final depth. Pull back the actual
reflected output at every arithmetic order, preserving both coefficient
maps and constructing the output on the quotient base change.
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
  retainedOlderLowerCoordinates retainedOlderFormulaIndex terminalLowerCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ} (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (k l : ℕ) (hk : k < j) (hl : l ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "a" => retainedOlderFormulaIndex j k hk
local notation "b" => (1 : Fin (j + 3))
local notation "d" => data ⟨k, Nat.lt_succ_of_le (hk.le.trans hj)⟩
local notation "e" => data ⟨l, Nat.lt_succ_of_le (hl.trans hj)⟩
local notation "f" => retainedOlderLowerCoordinates hπ data j hj k hk k le_rfl
local notation "g" => terminalLowerCoordinates hπ data j hj l hl
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj a b
local notation "input" => arithmeticRetainedTerminalFormulaInput hπ data m j hj k l hk hl
variable (hkl : k ≤ l) (hdepth : 2 * l ≤ depth) (hnear : depth ≤ k + 2 * l)
  (hsum : depth - k - l ≤ j) (h2 : W.a₂ = 0)
local notation "V" =>
  retainedTerminalReflectedOpen node data j hj k l hk hl hkl hdepth hnear hsum h2
local notation "add" =>
  retainedTerminalReflectedAddition node data j hj k l hk hl hkl hdepth hnear hsum h2

/-- Pull the actual reflected-depth domain back to the complete arithmetic retained pair. -/
def arithTerminalReflectedPositiveOpen : (pullback fa fb).Opens := P ⁻¹ᵁ V

local notation "D" => arithTerminalReflectedPositiveOpen node data m j hj k l hk hl
  hkl hdepth hnear hsum h2

/-- Construct a smooth output from the same full arithmetic inputs at every order. -/
def arithTerminalReflectedPositiveAddition : (D).toScheme ⟶ (U).toScheme := (P ∣_ V) ≫ add

/-- The output has precisely the original first arithmetic coefficient point. -/
@[reassoc] theorem arithTerminalReflectedPositiveAddition_structure :
    arithTerminalReflectedPositiveAddition node data m j hj k l hk hl hkl hdepth hnear hsum h2 ≫
      t =
      (D).ι ≫ pullback.fst fa fb ≫ fa ≫ q := by
  rw [arithTerminalReflectedPositiveAddition, Category.assoc,
    retainedTerminalReflectedAddition_structure]
  dsimp only [retainedTerminalReflectedInput]
  simp only [Category.assoc]
  rw [morphismRestrict_ι_assoc,
    finiteResolvedAtlasPairInput_fst_assoc, arithmeticAtlasPairPresentation_structure]
  simp only [Category.assoc, arithTerminalReflectedPositiveOpen]

/-- The same output has the original second arithmetic coefficient point. -/
@[reassoc] theorem arithTerminalReflectedPositiveAddition_structure_snd :
    arithTerminalReflectedPositiveAddition node data m j hj k l hk hl hkl hdepth hnear hsum h2 ≫
      t =
      (D).ι ≫ pullback.snd fa fb ≫ fb ≫ q := by
  rw [arithTerminalReflectedPositiveAddition_structure, pullback.condition_assoc]

/-- The constructed output lifts to the actual arithmetic base change of the smooth model. -/
def arithTerminalReflectedPositiveQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst fa fb ≫ fa)
    (arithTerminalReflectedPositiveAddition node data m j hj k l hk hl hkl hdepth hnear hsum h2)
    (by simpa only [Category.assoc] using
      (arithTerminalReflectedPositiveAddition_structure node data m j hj k l hk hl
        hkl hdepth hnear hsum h2).symm)

/-- The arithmetic output has the exact original quotient coefficient morphism. -/
@[reassoc] theorem arithTerminalReflectedPositiveQuotientOutput_base :
    arithTerminalReflectedPositiveQuotientOutput node data m j hj k l hk hl
        hkl hdepth hnear hsum h2 ≫ pullback.fst q t = (D).ι ≫ pullback.fst fa fb ≫ fa := by
  simp only [arithTerminalReflectedPositiveQuotientOutput, pullback.lift_fst]

/-- Projection recovers the entire constructed integral smooth output. -/
@[reassoc] theorem arithTerminalReflectedPositiveQuotientOutput_integral :
    arithTerminalReflectedPositiveQuotientOutput node data m j hj k l hk hl
        hkl hdepth hnear hsum h2 ≫ pullback.snd q t =
      arithTerminalReflectedPositiveAddition node data m j hj k l hk hl
      hkl hdepth hnear hsum h2 := by
  simp only [arithTerminalReflectedPositiveQuotientOutput, pullback.lift_snd]

local notation "al" => unequalPairLeft d e
local notation "ar" => unequalPairRight d e
local notation "x₁" => al (x W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "y₁" => al (y W (π ^ (0 + k)) (d).b3 (d).b4 (d).b6)
local notation "x₂" => ar (x W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)
local notation "y₂" => ar (y W (π ^ (0 + l)) (e).b3 (e).b4 (e).b6)

/-- Positive arithmetic branches are covered, including odd terminal inputs. -/
theorem arithTerminalReflectedPositiveOpen_mem (hk0 : 0 < k) (hlt : k < l)
    (hm : 2 * l < depth) (p : (pullback fa fb : Scheme))
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hy : y₁ ∈ (input p).asIdeal) (hv : y₂ ∈ (input p).asIdeal) : p ∈ D :=
  retainedTerminalReflectedOpen_positive_mem node data j hj k l hk hl hkl hdepth hnear hsum h2
    hk0 hlt hm (P p)
    (arithmeticRetainedTerminalFormulaInput_parameter_mem hπ data m j hj k l hk hl p)
    hx hu hy hv

/-- Positive arithmetic branches are covered, at even terminal depth. -/
theorem arithTerminalReflectedPositiveOpen_terminal_mem (hk0 : 0 < k) (hlt : k < l)
    (hm : depth = 2 * l) (p : (pullback fa fb : Scheme))
    (hx : x₁ ∉ (input p).asIdeal) (hu : x₂ ∉ (input p).asIdeal)
    (hy : y₁ ∈ (input p).asIdeal) : p ∈ D :=
  retainedTerminalReflectedOpen_terminal_mem node data j hj k l hk hl hkl hdepth hnear hsum h2
    hk0 hlt hm (P p)
    (arithmeticRetainedTerminalFormulaInput_parameter_mem hπ data m j hj k l hk hl p)
    hx hu hy

end FLT.Mazur.WeierstrassDividedDepth
