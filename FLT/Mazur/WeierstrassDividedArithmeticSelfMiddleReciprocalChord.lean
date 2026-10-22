/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSelfSmoothTangentAddition
public import FLT.Mazur.WeierstrassDividedMiddleReciprocalChordCoverage

/-!
# Full equal-retained-depth coverage at exact middle depth

The reciprocal chord source supplies the missing vertical outputs for retained
self-pairs. Together with the existing tangent domain it covers the whole
arithmetic product, with no puncture or coefficient-normalization assumption.
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
  retainedSelfFormulaCoordinates retainedSelfFormulaIndex
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {nodeDepth n : ℕ}
  (node : SplitNodeDepth W π nodeDepth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j ≤ n) (a : Option (Fin j))
local notation "hπ" => node.uniformizer_ne_zero
local notation "idx" => retainedSelfFormulaIndex j a
local notation "depth" => retainedSelfFormulaDepth j a
local notation "d" => data ⟨depth, Nat.lt_succ_of_le ((retainedSelfFormulaDepth_le j a).trans hj)⟩
local notation "f" => retainedSelfFormulaCoordinates hπ data j hj a
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m j hj
local notation "s" => finiteGlobalArithmeticStructure hπ data j hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q j hj idx
local notation "fa" => (O).ι ≫ chart idx ≫ s
local notation "coords" => tensorIntegralAtlasProjection hπ data Q j hj idx
local notation "P" => arithmeticAtlasPairPresentation hπ data m j hj idx idx
local notation "F" => retainedSelfFormulaInput hπ data j hj a
local notation "A" => DividedPairRing W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "input" => arithmeticSelfReciprocalFormulaInput hπ data m j hj a
local notation "al" => dividedPairLeft W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6
local notation "ar" => dividedPairRight W (π ^ (0 + depth)) (d).b3 (d).b4 (d).b6

local notation "V" => suppliedReciprocalChordDomain d al ar

/-- The actual reciprocal chord output domain in the full arithmetic retained self-product. -/
def arithmeticSelfReciprocalChordOpen : (pullback fa fa).Opens := input ⁻¹ᵁ V

local notation "D" => arithmeticSelfReciprocalChordOpen node data m j hj a

/-- The constructed original reciprocal chord output lifts to the entire supplied smooth model. -/
def arithmeticSelfReciprocalChordAddition : (D).toScheme ⟶ (U).toScheme :=
  (input ∣_ V) ≫ suppliedReciprocalChordResolvedAddition d al ar hπ data j hj

local notation "add" => arithmeticSelfReciprocalChordAddition node data m j hj a

/-- The entire reciprocal chord output preserves the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfReciprocalChordAddition_structure :
    add ≫ t = (D).ι ≫ pullback.fst fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfReciprocalChordAddition, Category.assoc,
    suppliedReciprocalChordResolvedAddition_structure, morphismRestrict_ι_assoc,
    arithmeticSelfFormulaInput_structure node data m j hj a]
  rfl

/-- The same output preserves the second original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticSelfReciprocalChordAddition_structure_snd :
    add ≫ t = (D).ι ≫ pullback.snd fa fa ≫ fa ≫ q := by
  rw [arithmeticSelfReciprocalChordAddition_structure, pullback.condition_assoc]

/-- The output retains its full original reciprocal chord contraction. -/
@[reassoc] theorem arithmeticSelfReciprocalChordAddition_contraction :
    add ≫ (U).ι ≫ finiteGlobalContraction hπ data j hj =
      (input ∣_ V) ≫ suppliedReciprocalChordOriginalSmooth d al ar ≫
        (WeierstrassIntegralChart.integralSmoothOpen W).ι := by
  rw [arithmeticSelfReciprocalChordAddition, Category.assoc,
    suppliedReciprocalChordResolvedAddition_contraction]

/-- The reciprocal chord output lifts over the original quotient, retaining its nilpotents. -/
def arithmeticSelfReciprocalChordQuotientOutput : (D).toScheme ⟶ pullback q t :=
  pullback.lift ((D).ι ≫ pullback.fst fa fa ≫ fa) add (by
    simpa only [Category.assoc] using
      (arithmeticSelfReciprocalChordAddition_structure node data m j hj a).symm)

/-- The quotient projection preserves the entire original coefficient morphism. -/
@[reassoc] theorem arithmeticSelfReciprocalChordQuotientOutput_base :
    arithmeticSelfReciprocalChordQuotientOutput node data m j hj a ≫ pullback.fst q t =
      (D).ι ≫ pullback.fst fa fa ≫ fa := by
  simp only [arithmeticSelfReciprocalChordQuotientOutput, pullback.lift_fst]

/-- The integral projection recovers the whole constructed smooth output. -/
@[reassoc] theorem arithmeticSelfReciprocalChordQuotientOutput_integral :
    arithmeticSelfReciprocalChordQuotientOutput node data m j hj a ≫ pullback.snd q t =
      add := by
  simp only [arithmeticSelfReciprocalChordQuotientOutput, pullback.lift_snd]

local notation "T" => arithmeticSelfSmoothTangentOpen node data m j hj a
local notation "den" => dividedTangentDenominator W (π ^ (0 + depth))
  (d).b3 (d).b4 (d).b6 al ar

/-- Every exact-middle retained pair with vanishing tangent denominator has an actual output. -/
theorem arithmeticSelfReciprocalChordOpen_middle_mem
    (hd0 : 0 < depth) (hm : 2 * depth = nodeDepth) (p : (pullback fa fa : Scheme))
    (hd : den ∈ (input p).asIdeal) : p ∈ D := by
  exact suppliedReciprocalChordDomain_middle_mem node d al ar
    (by change 0 < 0 + depth; omega) (by change 2 * (0 + depth) = nodeDepth; omega)
    (input p) (arithmeticSelfFormulaInput_parameter_mem node data m j hj a p) hd

/-- Equal retained depths have full middle-depth coverage, including zero-abscissa self-pairs. -/
theorem arithmeticSelf_middle_cover (hd0 : 0 < depth) (hm : 2 * depth = nodeDepth)
    (p : (pullback fa fa : Scheme)) : p ∈ T ∨ p ∈ D := by
  exact middleTangentReciprocalChord_cover node d al ar
    (by change 0 < 0 + depth; omega) (by change 2 * (0 + depth) = nodeDepth; omega)
    (input p) (arithmeticSelfFormulaInput_parameter_mem node data m j hj a p)

/-- The two genuine output domains exhaust the original arithmetic retained self-product. -/
theorem arithmeticSelf_middle_top (hd0 : 0 < depth) (hm : 2 * depth = nodeDepth) :
    T ⊔ D = ⊤ := by
  apply top_unique
  intro p _
  exact arithmeticSelf_middle_cover node data m j hj a hd0 hm p

end FLT.Mazur.WeierstrassDividedDepth
