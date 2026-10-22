/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedOddIncidence
public import FLT.Mazur.WeierstrassDividedArithmeticMixedNodalReflectedCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticSmoothPairInclusion

/-!
# Actual local sources for the odd last-retained/terminal pair

Join the three unshifted normalized domains with both terminal incidence
sources. Each embeds openly in the original pair and retains its quotient output.
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
local notation "O" => arithmeticLastRetainedPairOpen node data m j hj g'
local notation "D" => arithmeticLastRetainedMiddleSmoothOpen node data m j hj
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
variable (hodd : depth = 2 * (j + 1) + 1) (hj0 : 0 < j)
local notation "E" => arithmeticMixedNodalReflectedChart node data m (j + 1) hj
  j (Nat.lt_succ_self j) (by omega) (by omega)
local notation "C" => arithmeticLastRetainedOddIncidenceChart node data m j hj hodd

/-- Three unshifted formulas and two transferred terminal formulas. -/
abbrev LastRetainedOddLocalIndex := Sum (Fin 3) Bool

/-- Genuine formula domains, retaining their original source schemes. -/
def arithmeticLastRetainedOddLocalSource : LastRetainedOddLocalIndex → Scheme
  | .inl c => (E c).toScheme
  | .inr b => (C b).toScheme

local notation "X" => arithmeticLastRetainedOddLocalSource node data m j hj hodd hj0

/-- Both kinds of source embed into the same full original ordered pair. -/
def arithmeticLastRetainedOddLocalInclusion :
    (c : LastRetainedOddLocalIndex) → X c ⟶ pullback f g'
  | .inl c => (E c).ι ≫ I
  | .inr b => (C b).ι ≫ (D).ι ≫ (O).ι

local notation "J" => arithmeticLastRetainedOddLocalInclusion node data m j hj hodd hj0

/-- These are open embeddings of actual sources, not merely pointwise formulas. -/
instance arithmeticLastRetainedOddLocalInclusion_open (c : LastRetainedOddLocalIndex) :
    IsOpenImmersion (J c) := by
  cases c <;> dsimp only [arithmeticLastRetainedOddLocalInclusion] <;> infer_instance

/-- Every source carries a whole normalized output over the arithmetic quotient. -/
def arithmeticLastRetainedOddLocalOutput :
    (c : LastRetainedOddLocalIndex) → X c ⟶ pullback q t
  | .inl c => arithmeticMixedNodalReflectedQuotientOutput node data m (j + 1) hj
      j (Nat.lt_succ_self j) (by omega) (by omega) c
  | .inr b => arithmeticLastRetainedOddIncidenceOutput node data m j hj hodd b

/-- All coefficients, including nilpotents, agree with the original input map. -/
@[reassoc] theorem arithmeticLastRetainedOddLocalOutput_base (c : LastRetainedOddLocalIndex) :
    arithmeticLastRetainedOddLocalOutput node data m j hj hodd hj0 c ≫ pullback.fst q t =
      J c ≫ pullback.fst f g' ≫ f := by
  cases c <;>
    simp only [arithmeticLastRetainedOddLocalOutput, arithmeticLastRetainedOddLocalInclusion,
      Category.assoc, arithmeticMixedNodalReflectedQuotientOutput_base,
      arithmeticLastRetainedOddIncidenceOutput_base, arithmeticSmoothPairInclusion_first_assoc]

end FLT.Mazur.WeierstrassDividedDepth
