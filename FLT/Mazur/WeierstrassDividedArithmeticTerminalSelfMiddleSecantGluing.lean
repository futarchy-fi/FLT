/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfMiddleGluing
public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfMiddleSecant
public import FLT.Mazur.WeierstrassDividedReciprocalChordSecantSmooth

/-!
# The middle secant law is a restriction of glued terminal addition

Compare whole quotient outputs on both actual chart overlaps, then descend
the equality over the pulled-back two-chart cover of the full secant domain.
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

local notation "C" => arithmeticTerminalSelfReciprocalChordOpen hπ data m j hj
local notation "T" => arithmeticTerminalSelfSmoothTangentOpen hπ data m j hj
local notation "ca" => arithmeticTerminalSelfReciprocalChordAddition hπ data m j hj
local notation "ta" => arithmeticTerminalSelfSmoothTangentAddition hπ data m j hj
local notation "cq" => arithmeticTerminalSelfReciprocalChordQuotientOutput hπ data m j hj
local notation "tq" => arithmeticTerminalSelfSmoothTangentQuotientOutput hπ data m j hj

local notation "S" => arithmeticTerminalSelfSmoothSecantOpen hπ data m j hj
local notation "sa" => arithmeticTerminalSelfSmoothSecantAddition hπ data m j hj
local notation "sq" => arithmeticTerminalSelfSmoothSecantQuotientOutput hπ data m j hj
local notation "D" => arithmeticTerminalSelfMiddleChart hπ data m j hj
local notation "out" => arithmeticTerminalSelfMiddleChartOutput hπ data m j hj
local notation "sv" => suppliedSmoothSecantDomain d al ar

/-- Both middle chart laws agree with the whole secant quotient output on arbitrary overlaps. -/
theorem arithmeticTerminalSelfMiddleChart_secant (b : Bool) {X : Scheme}
    (f : X ⟶ (D b).toScheme) (g : X ⟶ (S).toScheme)
    (h : f ≫ (D b).ι = g ≫ (S).ι) : f ≫ out b = g ≫ sq := by
  apply pullback.hom_ext
  · simp only [Category.assoc, arithmeticTerminalSelfMiddleChartOutput_base,
      arithmeticTerminalSelfSmoothSecantQuotientOutput_base]
    exact congrArg (fun z => z ≫ pullback.fst fa fa ≫ fa) h
  · cases b
    · have he := suppliedReciprocalChordSecant_resolved d al ar hπ data j hj
        (f ≫ (input ∣_ V)) (g ≫ (input ∣_ sv)) (by
          simpa only [Category.assoc, morphismRestrict_ι,
            arithmeticTerminalSelfMiddleChart, arithmeticTerminalSelfReciprocalChordOpen,
            arithmeticTerminalSelfSmoothSecantOpen] using congrArg (fun z => z ≫ input) h)
      simpa only [Category.assoc, arithmeticTerminalSelfMiddleChartOutput,
        arithmeticTerminalSelfReciprocalChordQuotientOutput_integral,
        arithmeticTerminalSelfSmoothSecantQuotientOutput_integral,
        arithmeticTerminalSelfReciprocalChordAddition,
        arithmeticTerminalSelfSmoothSecantAddition] using he
    · have he := suppliedTangentSecant_resolved d al ar hπ data j hj
        (f ≫ (input ∣_ suppliedSmoothTangentDomain d al ar)) (g ≫ (input ∣_ sv)) (by
          simpa only [Category.assoc, morphismRestrict_ι,
            arithmeticTerminalSelfMiddleChart, arithmeticTerminalSelfSmoothTangentOpen,
            arithmeticTerminalSelfSmoothSecantOpen] using congrArg (fun z => z ≫ input) h)
      simpa only [Category.assoc, arithmeticTerminalSelfMiddleChartOutput,
        arithmeticTerminalSelfSmoothTangentQuotientOutput_integral,
        arithmeticTerminalSelfSmoothSecantQuotientOutput_integral,
        arithmeticTerminalSelfSmoothTangentAddition,
        arithmeticTerminalSelfSmoothSecantAddition] using he

variable [IsLocalRing R] {depth : ℕ} (node : SplitNodeDepth W π depth)
  (hj0 : 0 < j) (hm : 2 * j = depth)
local notation "cover" => arithmeticTerminalSelfMiddleCover hπ data m j hj node hj0 hm
local notation "add" => arithmeticTerminalSelfMiddleAddition hπ data m j hj node hj0 hm

/-- The entire secant formula agrees with the glued law, including its nilpotent coefficients. -/
@[reassoc] theorem arithmeticTerminalSelfMiddleAddition_secant : (S).ι ≫ add = sq := by
  apply Scheme.Cover.hom_ext ((cover).pullback₁ (S).ι)
  intro b
  have hi : (cover).pullbackHom (S).ι b ≫ (D b).ι =
      ((cover).pullback₁ (S).ι).f b ≫ (S).ι := (cover).pullbackHom_map (S).ι b
  have he := arithmeticTerminalSelfMiddleChart_secant hπ data m j hj b
    ((cover).pullbackHom (S).ι b) (((cover).pullback₁ (S).ι).f b) hi
  have hr := congrArg (fun z => z ≫ add) hi.symm
  have hr' : ((cover).pullback₁ (S).ι).f b ≫ (S).ι ≫ add =
      (cover).pullbackHom (S).ι b ≫ out b := by
    simpa only [Category.assoc, arithmeticTerminalSelfMiddleAddition_chart] using hr
  exact hr'.trans he

end FLT.Mazur.WeierstrassDividedDepth
