/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSeparatedFlexiblePreMiddleOutputCover
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedAdjacentFlexiblePreMiddleOutputCover

/-!
# Smaller final stages for all positive unequal retained inputs

Combine the adjacent and separated constructions without losing either
coefficient map. The exact stage requirement gives explicit smaller-stage
contracts near the middle and throughout the reflected range.
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
  (m k : ℕ) (hk : k ≤ n) (i j : ℕ) (hlt : i < j)
  (hpre : 2 * (j + 2) < depth)
  (hstage : arithmeticFlexiblePairStage i j depth ≤ k)
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
include hlt hpre hstage hgen

/-- Every increasing positive retained pair has a whole quotient output cover. -/
theorem arithmeticRetainedUnequalFlexibleOutputCover :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (r : C.I₀) → C.X r ⟶ pullback q t),
      ∀ r, out r ≫ pullback.fst q t = C.f r ≫ pullback.fst fa fb ≫ fa := by
  by_cases he : j = i + 1
  · subst j
    exact arithmeticRetainedAdjacentFlexiblePreMiddleOutputCover
      node data m k hk i (by omega) hstage hgen
  · exact arithmeticRetainedSeparatedFlexiblePreMiddleOutputCover
      node data m k hk i j (by omega) hpre hstage hgen

/-- One family of actual outputs retains both entire coefficient morphisms. -/
theorem arithmeticRetainedUnequalFlexibleOutputCover_both :
    ∃ (C : (pullback fa fb : Scheme).OpenCover.{0})
      (out : (r : C.I₀) → C.X r ⟶ pullback q t),
      ∀ r, (out r ≫ pullback.fst q t = C.f r ≫ pullback.fst fa fb ≫ fa) ∧
        (out r ≫ pullback.fst q t = C.f r ≫ pullback.snd fa fb ≫ fb) := by
  obtain ⟨C, out, h⟩ := arithmeticRetainedUnequalFlexibleOutputCover
    node data m k hk i j hlt hpre hstage hgen
  exact ⟨C, out, fun r => ⟨h r, by rw [h, pullback.condition]⟩⟩

/-- The reversed inputs have the same complete coefficient-preserving cover. -/
theorem arithmeticRetainedUnequalFlexibleReversedOutputCover :
    ∃ (C : (pullback fb fa : Scheme).OpenCover.{0})
      (out : (r : C.I₀) → C.X r ⟶ pullback q t),
      ∀ r, out r ≫ pullback.fst q t = C.f r ≫ pullback.fst fb fa ≫ fb := by
  obtain ⟨C, out, h⟩ := arithmeticRetainedUnequalFlexibleOutputCover
    node data m k hk i j hlt hpre hstage hgen
  exact schemeQuotientOutputCover_swap (pullback.fst q t) fa fb C out h

end FLT.Mazur.WeierstrassDividedDepth
