/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedZeroStageOriginalGluing

/-!
# The complete glued stage-zero law over every arithmetic quotient

Base change the glued integral law on the entire resolved smooth product.
Every original arithmetic atlas pair maps into that full domain, and its
whole local action output is exactly the restriction of the glued law.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  globalIntegralAtlasObject globalIntegralAtlasMap globalSmoothAtlasOpen globalSmoothAtlasMap
  globalTensorAtlasObject arithmeticTensorAtlasMap tensorIntegralAtlasProjection
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val)) (m : ℕ)
local notation "hj" => Nat.zero_le n
local notation "base" => finiteGlobalStructure hπ data 0 hj
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "σ" => pullback.fst t t ≫ t
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "add" => zeroStageOriginalAddition hπ data

/-- The complete stage-zero addition over the original quotient, including nilpotents. -/
def arithmeticZeroStageGlobalAddition : pullback q σ ⟶ pullback q t :=
  pullback.lift (pullback.fst q σ) (pullback.snd q σ ≫ add) (by
    rw [Category.assoc, zeroStageOriginalAddition_structure]
    exact pullback.condition)

local notation "arith" => arithmeticZeroStageGlobalAddition hπ data m

/-- The glued arithmetic law retains its entire original quotient structure morphism. -/
@[reassoc] theorem arithmeticZeroStageGlobalAddition_base :
    arith ≫ pullback.fst q t = pullback.fst q σ := pullback.lift_fst _ _ _

/-- Integral projection recovers the actual glued stage-zero law. -/
@[reassoc] theorem arithmeticZeroStageGlobalAddition_integral :
    arith ≫ pullback.snd q t = pullback.snd q σ ≫ add := pullback.lift_snd _ _ _

variable (a b : Fin 3)
local notation "chart" => arithmeticTensorAtlasMap hπ data m 0 hj
local notation "s" => finiteGlobalArithmeticStructure hπ data 0 hj m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q 0 hj
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
local notation "P" => arithmeticAtlasPairPresentation hπ data m 0 hj a b
local notation "I" => finiteResolvedAtlasPairInput hπ data 0 hj a b

/-- Both complete arithmetic atlas inputs present the full base-changed smooth product. -/
def arithmeticZeroStagePairToGlobal : pullback fa fb ⟶ pullback q σ :=
  pullback.lift (pullback.fst fa fb ≫ fa) (P ≫ I) (by
    simp only [Category.assoc, finiteResolvedAtlasPairInput_fst_assoc]
    exact (arithmeticAtlasPairPresentation_structure hπ data m 0 hj a b).symm)

local notation "pair" => arithmeticZeroStagePairToGlobal hπ data m a b

/-- The pair presentation retains the complete original quotient coefficient map. -/
@[reassoc] theorem arithmeticZeroStagePairToGlobal_base :
    pair ≫ pullback.fst q σ = pullback.fst fa fb ≫ fa := pullback.lift_fst _ _ _

/-- The integral projection retains both full original resolved inputs. -/
@[reassoc] theorem arithmeticZeroStagePairToGlobal_integral :
    pair ≫ pullback.snd q σ = P ≫ I := pullback.lift_snd _ _ _

/-- Every whole local arithmetic output is a restriction of the glued quotient-valued law. -/
@[reassoc] theorem arithmeticZeroStageGlobalAddition_pair :
    pair ≫ arith = arithmeticZeroStageActionQuotientOutput hπ data m a b := by
  apply pullback.hom_ext
  · rw [Category.assoc, arithmeticZeroStageGlobalAddition_base,
      arithmeticZeroStagePairToGlobal_base, arithmeticZeroStageActionQuotientOutput_base]
  · rw [Category.assoc, arithmeticZeroStageGlobalAddition_integral,
      arithmeticZeroStagePairToGlobal_integral_assoc, zeroStageOriginalAddition_pair,
      arithmeticZeroStageActionQuotientOutput_integral]
    rfl

/-- Equal whole pair presentations give identical arithmetic outputs on every test scheme. -/
theorem arithmeticZeroStageActionQuotientOutput_common (a' b' : Fin 3) {X : Scheme}
    (f : X ⟶ pullback fa fb)
    (g : X ⟶ pullback ((O a').ι ≫ chart a' ≫ s) ((O b').ι ≫ chart b' ≫ s))
    (h : f ≫ pair = g ≫ arithmeticZeroStagePairToGlobal hπ data m a' b') :
    f ≫ arithmeticZeroStageActionQuotientOutput hπ data m a b =
      g ≫ arithmeticZeroStageActionQuotientOutput hπ data m a' b' := by
  rw [← arithmeticZeroStageGlobalAddition_pair, ← arithmeticZeroStageGlobalAddition_pair]
  simpa only [Category.assoc] using congrArg (fun morphism => morphism ≫ arith) h

end FLT.Mazur.WeierstrassDividedDepth
