/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedUnequalFlexibleOutputCover

/-!
# Exact minimum-stage contracts for retained quotient covers

Choose the smallest stage permitted by the existing three-depth transfer
construction. This proves covers of the original model at that stage; no
comparison with a larger resolved model is assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticFixedAdjacentTargetCoordinates
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m i j : ℕ) (hlt : i < j) (hpre : 2 * (j + 2) < depth)
  (hk : arithmeticFlexiblePairStage i j depth ≤ n)
local notation "k" => arithmeticFlexiblePairStage i j depth
local notation "hstage" => (le_refl k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "O" => tensorIntegralAtlasSmoothOpen hπ data Q k hk
local notation "a" => retainedOlderFormulaIndex k (i + 1)
  (by have := ((arithmeticFlexiblePairStage_le_iff i j depth k).mp hstage).1; omega)
local notation "b" => retainedOlderFormulaIndex k (j + 1)
  (by have := ((arithmeticFlexiblePairStage_le_iff i j depth k).mp hstage).1; omega)
local notation "fa" => (O a).ι ≫ chart a ≫ s
local notation "fb" => (O b).ι ≫ chart b ≫ s
variable (hgen : IsLocalRing.maximalIdeal R = ideal R π)
include hlt hpre hgen

/-- The exact stage bound constructs outputs on the entire smooth pair at that stage. -/
theorem arithmeticRetainedUnequalMinimumStageOutputCover :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (r : C.I₀) → C.X r ⟶ pullback q t),
      ∀ r, (out r ≫ pullback.fst q t = C.f r ≫ pullback.fst fa fb ≫ fa) ∧
        (out r ≫ pullback.fst q t = C.f r ≫ pullback.snd fa fb ≫ fb) := by
  exact arithmeticRetainedUnequalFlexibleOutputCover_both
    node data m k hk i j hlt hpre hstage hgen

/-- Exchanging inputs at the minimum stage also has an actual whole quotient cover. -/
theorem arithmeticRetainedUnequalMinimumStageReversedOutputCover :
    ∃ (C : (pullback fb fa : Scheme).OpenCover.{0})
      (out : (r : C.I₀) → C.X r ⟶ pullback q t),
      ∀ r, out r ≫ pullback.fst q t = C.f r ≫ pullback.fst fb fa ≫ fb := by
  exact arithmeticRetainedUnequalFlexibleReversedOutputCover
    node data m k hk i j hlt hpre hstage hgen

end FLT.Mazur.WeierstrassDividedDepth
