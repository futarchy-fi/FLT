/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedMiddleZeroCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticSmoothPairInclusion
public import FLT.Mazur.WeierstrassDividedArithmeticMixedHorizontalCoverage

/-!
# Two actual output sources for the full last-retained/middle-terminal pair

The difference formula covers the retained puncture. The constructed terminal
transfer covers its smooth complement. Both carry complete quotient outputs.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => retainedOlderFormulaIndex (j + 1) j (Nat.lt_succ_self j)
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "E" => finiteDividedTensorAtlasIso hπ data Q (j + 1) hj
local notation "f" => chart a ≫ s
local notation "f₀" => old ≫ s
local notation "f'" => next ≫ s
local notation "g'" => chart 1 ≫ s
local notation "coords" => arithmeticLastRetainedIndexedCoordinates node data m j hj



local notation "A" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj
local notation "fa" => (A a).ι ≫ chart a ≫ s
local notation "fb" => (A 1).ι ≫ chart 1 ≫ s
local notation "I" => arithmeticSmoothPairInclusion hπ data m (j + 1) hj a 1
local notation "V" => arithmeticRetainedTerminalOpen hπ data m (j + 1) hj
  j (j + 1) (Nat.lt_succ_self j) le_rfl (Nat.le_succ j)
local notation "add" => arithmeticRetainedTerminalAddition hπ data m (j + 1) hj
  j (j + 1) (Nat.lt_succ_self j) le_rfl (Nat.le_succ j)
local notation "O" => arithmeticLastRetainedPairOpen node data m j hj g'
local notation "D" => arithmeticLastRetainedMiddleSmoothOpen node data m j hj
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- The two actual formula sources, without any claim that their outputs agree. -/
def arithmeticLastRetainedMiddleLocalSource : Bool → Scheme
  | false => (V).toScheme
  | true => (D).toScheme

local notation "X" => arithmeticLastRetainedMiddleLocalSource node data m j hj

/-- Both source inclusions retain the full original ordered arithmetic pair. -/
def arithmeticLastRetainedMiddleLocalInclusion : (b : Bool) → X b ⟶ pullback f g'
  | false => (V).ι ≫ I
  | true => (D).ι ≫ (O).ι

local notation "inc" => arithmeticLastRetainedMiddleLocalInclusion node data m j hj

/-- Each formula source is an actual open subchart of the entire original pair. -/
instance arithmeticLastRetainedMiddleLocalInclusion_open (b : Bool) :
    IsOpenImmersion (inc b) := by
  cases b <;> dsimp only [arithmeticLastRetainedMiddleLocalInclusion] <;> infer_instance

variable (hm : 2 * (j + 1) = depth)

/-- Both local formulas are whole morphisms over the original arithmetic quotient. -/
def arithmeticLastRetainedMiddleLocalOutput : (b : Bool) → X b ⟶ pullback q t
  | false => pullback.lift ((V).ι ≫ pullback.fst fa fb ≫ fa) add (by
      simpa only [Category.assoc] using
        (arithmeticRetainedTerminalAddition_structure hπ data m (j + 1) hj
          j (j + 1) (Nat.lt_succ_self j) le_rfl (Nat.le_succ j)).symm)
  | true => arithmeticLastRetainedMiddleQuotientOutput node data m j hj hm

/-- Each output keeps the complete original first arithmetic coefficient map. -/
@[reassoc] theorem arithmeticLastRetainedMiddleLocalOutput_base (b : Bool) :
    arithmeticLastRetainedMiddleLocalOutput node data m j hj hm b ≫ pullback.fst q t =
      inc b ≫ pullback.fst f g' ≫ f := by
  cases b
  · simp only [arithmeticLastRetainedMiddleLocalOutput, pullback.lift_fst,
      arithmeticLastRetainedMiddleLocalInclusion, Category.assoc,
      arithmeticSmoothPairInclusion_first_assoc]
  · exact arithmeticLastRetainedMiddleQuotientOutput_base node data m j hj hm

local instance arithmeticLastRetainedMiddleLocal_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "u" => tensorCoord W (π ^ (0 + j)) π (e).b3 (e).b4 (e).b6 Q 2

include hm in
/-- Every smooth original last-retained/middle-terminal pair reaches an actual output source. -/
theorem arithmeticLastRetainedMiddleLocal_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (pullback f g' : Scheme))
    (hs : chart a (pullback.fst f g' p) ∈ (s).smoothLocus)
    (ht : chart 1 (pullback.snd f g' p) ∈ (s).smoothLocus) :
    ∃ b, ∃ z : X b, inc b z = p := by
  classical
  by_cases hx : u ∈ (coords (pullback.fst f g' p)).asIdeal
  · obtain ⟨z, hz⟩ := arithmeticLastRetainedMiddleSmoothOpen_zero_exists
      node data m j hj hgen hm p hs ht hx
    exact ⟨true, z, hz⟩
  · obtain ⟨z, hz⟩ := arithmeticSmoothPairInclusion_exists hπ data m (j + 1) hj a 1 p hs ht
    have he : (A a).ι (pullback.fst fa fb z) = pullback.fst f g' p := by
      have hi := congrArg (fun morphism => morphism z)
        (arithmeticSmoothPairInclusion_first hπ data m (j + 1) hj a 1)
      exact hi.symm.trans (congrArg (pullback.fst f g') hz)
    have hv : z ∈ V := by
      apply arithmeticMixed_horizontal_middle_mem hπ data m (j + 1) hj j
        (Nat.lt_succ_self j) node hm z
      erw [← arithmeticLastRetainedIndexedCoordinates, he]
      exact hx
    exact ⟨false, ⟨z, hv⟩, hz⟩

end FLT.Mazur.WeierstrassDividedDepth
