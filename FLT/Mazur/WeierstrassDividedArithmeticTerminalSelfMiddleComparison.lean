/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalSelfMiddleReciprocalChord
public import FLT.Mazur.WeierstrassDividedReciprocalChordTangentSmooth

/-!
# Whole arithmetic terminal reciprocal chord/tangent agreement

The two output formulas agree after arbitrary refinement of the original
arithmetic terminal self-product, including its nonreduced quotient output.
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

/-- Equality in the full resolved smooth model on every common scheme refinement. -/
theorem arithmeticTerminalSelfMiddle_resolved_eq {X : Scheme}
    (f : X ⟶ (C).toScheme) (g : X ⟶ (T).toScheme) (h : f ≫ (C).ι = g ≫ (T).ι) :
    f ≫ ca = g ≫ ta := by
  have he := suppliedReciprocalChordTangent_resolved d al ar hπ data j hj
    (f ≫ (input ∣_ V)) (g ≫ (input ∣_ suppliedSmoothTangentDomain d al ar)) (by
      simpa only [Category.assoc, morphismRestrict_ι,
        arithmeticTerminalSelfReciprocalChordOpen, arithmeticTerminalSelfSmoothTangentOpen]
        using congrArg (fun z => z ≫ input) h)
  simpa only [arithmeticTerminalSelfReciprocalChordAddition,
    arithmeticTerminalSelfSmoothTangentAddition, Category.assoc] using he

/-- Equality retains the whole quotient-valued output, rather than only its residue points. -/
theorem arithmeticTerminalSelfMiddle_quotient_eq {X : Scheme}
    (f : X ⟶ (C).toScheme) (g : X ⟶ (T).toScheme) (h : f ≫ (C).ι = g ≫ (T).ι) :
    f ≫ cq = g ≫ tq := by
  apply pullback.hom_ext
  · simp only [Category.assoc, arithmeticTerminalSelfReciprocalChordQuotientOutput_base,
      arithmeticTerminalSelfSmoothTangentQuotientOutput_base]
    exact congrArg (fun z => z ≫ pullback.fst fa fa ≫ fa) h
  · simp only [Category.assoc, arithmeticTerminalSelfReciprocalChordQuotientOutput_integral,
      arithmeticTerminalSelfSmoothTangentQuotientOutput_integral]
    exact arithmeticTerminalSelfMiddle_resolved_eq hπ data m j hj f g h

/-- In particular the actual fiber-product overlap has equal quotient outputs. -/
theorem arithmeticTerminalSelfMiddle_overlap :
    pullback.fst (C).ι (T).ι ≫ cq = pullback.snd (C).ι (T).ι ≫ tq :=
  arithmeticTerminalSelfMiddle_quotient_eq hπ data m j hj _ _ pullback.condition

end FLT.Mazur.WeierstrassDividedDepth
