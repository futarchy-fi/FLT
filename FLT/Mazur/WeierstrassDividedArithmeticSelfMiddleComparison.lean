/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticSelfMiddleReciprocalChord
public import FLT.Mazur.WeierstrassDividedReciprocalChordTangentSmooth

/-!
# Equal-retained-depth output compatibility

Keep the existing two-step tangent restriction and compare its whole quotient
output with the reciprocal chord output on arbitrary refinements.
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

local notation "C" => arithmeticSelfReciprocalChordOpen node data m j hj a
local notation "T" => arithmeticSelfSmoothTangentOpen node data m j hj a
local notation "ca" => arithmeticSelfReciprocalChordAddition node data m j hj a
local notation "ta" => arithmeticSelfSmoothTangentAddition node data m j hj a
local notation "cq" => arithmeticSelfReciprocalChordQuotientOutput node data m j hj a

/-- The existing tangent output lifts over the entire original quotient. -/
def arithmeticSelfSmoothTangentQuotientOutput : (T).toScheme ⟶ pullback q t :=
  pullback.lift ((T).ι ≫ pullback.fst fa fa ≫ fa) ta (by
    simpa only [Category.assoc] using
      (arithmeticSelfSmoothTangentAddition_structure node data m j hj a).symm)

local notation "tq" => arithmeticSelfSmoothTangentQuotientOutput node data m j hj a

/-- The quotient projection retains the original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticSelfSmoothTangentQuotientOutput_base :
    tq ≫ pullback.fst q t = (T).ι ≫ pullback.fst fa fa ≫ fa := by
  simp only [arithmeticSelfSmoothTangentQuotientOutput, pullback.lift_fst]

/-- The integral projection recovers the whole existing tangent law. -/
@[reassoc] theorem arithmeticSelfSmoothTangentQuotientOutput_integral :
    tq ≫ pullback.snd q t = ta := by
  simp only [arithmeticSelfSmoothTangentQuotientOutput, pullback.lift_snd]

/-- Any common scheme refinement has equal outputs in the full finite smooth model. -/
theorem arithmeticSelfMiddle_resolved_eq {X : Scheme}
    (f : X ⟶ (C).toScheme) (g : X ⟶ (T).toScheme) (h : f ≫ (C).ι = g ≫ (T).ι) :
    f ≫ ca = g ≫ ta := by
  let vt := retainedSelfSmoothTangentOpen hπ data j hj a
  let tv := suppliedSmoothTangentDomain d al ar
  have he := suppliedReciprocalChordTangent_resolved d al ar hπ data j hj
    (f ≫ (input ∣_ V)) (g ≫ (P ∣_ vt) ≫ (F ∣_ tv)) (by
      have hh := congrArg (fun z => z ≫ input) h
      simpa only [tv, vt, retainedSelfSmoothTangentOpen, atlasPairSmoothTangentOpen,
        retainedSelfFormulaInput, Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc,
        arithmeticSelfReciprocalChordOpen, arithmeticSelfSmoothTangentOpen,
        arithmeticSelfReciprocalFormulaInput] using hh)
  simpa only [arithmeticSelfReciprocalChordAddition,
    arithmeticSelfSmoothTangentAddition, retainedSelfSmoothTangentAddition,
    atlasPairSmoothTangentAddition, retainedSelfFormulaInput, Category.assoc, vt, tv] using he

/-- Agreement retains both projections of the original nonreduced quotient output. -/
theorem arithmeticSelfMiddle_quotient_eq {X : Scheme}
    (f : X ⟶ (C).toScheme) (g : X ⟶ (T).toScheme) (h : f ≫ (C).ι = g ≫ (T).ι) :
    f ≫ cq = g ≫ tq := by
  apply pullback.hom_ext
  · simp only [Category.assoc, arithmeticSelfReciprocalChordQuotientOutput_base,
      arithmeticSelfSmoothTangentQuotientOutput_base]
    exact congrArg (fun z => z ≫ pullback.fst fa fa ≫ fa) h
  · simp only [Category.assoc, arithmeticSelfReciprocalChordQuotientOutput_integral,
      arithmeticSelfSmoothTangentQuotientOutput_integral]
    exact arithmeticSelfMiddle_resolved_eq node data m j hj a f g h

end FLT.Mazur.WeierstrassDividedDepth
