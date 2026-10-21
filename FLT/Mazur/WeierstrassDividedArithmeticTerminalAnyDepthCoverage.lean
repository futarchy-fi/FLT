/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTerminalPairTransfer
public import FLT.Mazur.WeierstrassSuccessiveXArithmeticSmoothCover
public import FLT.Mazur.WeierstrassDividedArithmeticNewestIndex
public import FLT.Mazur.PrincipalOpenTensorRange
public import FLT.Mazur.SchemePairBoundaryTransfer

/-!
# Full arithmetic terminal coverage at every creation depth

Every smooth nonpunctured terminal source belongs to the actual incidence
transfer domain. The transferred divided input is punctured, and both original
arithmetic inputs survive unchanged at every quotient order.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages WeierstrassSuccessiveX
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  [IsNoetherianRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
  (hgen : IsLocalRing.maximalIdeal R = ideal R π)
  (m j : ℕ) (hj : j + 1 ≤ n)
local notation "Q" => Quotient R π m
local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "x" => WeierstrassDilatation.x W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e)
local notation "t" => coord W (π ^ (start + j)) π (Data.b3 e) (Data.b4 e) (Data.b6 e) 0
local notation "tt" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 0
local notation "tu" => WeierstrassDilatation.tensorX W (π ^ (start + j + 1))
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q
local notation "A" => PrincipalOpenTensor.transitionIso Q x t
  (depthOverlapEquiv W π (start + j) (Data.b3 e) (Data.b4 e) (Data.b6 e))
local notation "a" => PrincipalOpenTensor.inclusion Q t
local notation "b" => (A).hom ≫ PrincipalOpenTensor.inclusion Q x
local notation "old" => finiteArithmeticNewestTensorChart hπ data m j hj
local notation "next" => finiteArithmeticDividedTensorChart hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local instance arithmeticTerminalCoverage_structure : LocallyOfFinitePresentation s := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local instance arithmeticTerminalCoverage_open : IsOpenImmersion old := by
  rw [← finiteArithmeticOlderTensorChart_zero hπ data j hj m]
  exact finiteArithmeticOlderTensorChart_isOpenImmersion hπ data m j hj 0 hj

local notation "f" => old ≫ s
local notation "f'" => next ≫ s
local notation "H" => (terminalArithmeticTensor_isPullback hπ data m j hj).flip
variable {Y : Scheme}
  (g : Y ⟶ Spec (.of (PolygonArithmeticStages.Quotient R π m)))

local notation "O" => arithmeticTerminalPairOpen hπ data m j hj g
local notation "transfer" => arithmeticTerminalPairTransfer hπ data m j hj g
local notation "oldU" => tensorCoord W (π ^ (start + j)) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2

include D hgen in
/-- Both original opens cover exactly the smooth arithmetic first input, at any depth. -/
theorem arithmeticTerminalPairOpen_anyDepth_smooth_iff
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme)) :
    old (pullback.fst f g p) ∈ (s).smoothLocus ↔
      oldU ∉ (pullback.fst f g p).asIdeal ∨ p ∈ O := by
  rw [arithmeticTerminalPairOpen_mem]
  exact (arithmeticAnyDepth_chart_mem_smooth_iff D hπ hgen (start + j) hk
    (Data.b3 e) (Data.b4 e) (Data.b6 e) (Data.factor3 e) (Data.factor4 e) m old s
    (by rw [← finiteArithmeticOlderTensorChart_zero hπ data j hj m]
        exact finiteArithmeticOlderTensorChart_structure hπ data m j hj 0 hj) _).trans or_comm

include D hgen in
/-- A smooth arithmetic input with zero horizontal coordinate lies in the actual boundary. -/
theorem arithmeticTerminalPairOpen_anyDepth_zero_mem
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (hz : oldU ∈ (pullback.fst f g p).asIdeal) : p ∈ O := by
  have he := (arithmeticTerminalPairOpen_anyDepth_smooth_iff
    hπ data D hgen m j hj g hk p).mp hs
  exact he.resolve_left (not_not.mpr hz)

include D hgen in
/-- The actual arithmetic pair acquires a punctured first input without changing either input. -/
theorem arithmeticTerminalPair_anyDepth_zero_coordinates
    (hk : 2 * (start + j + 1) ≤ depth) (p : (pullback f g : Scheme))
    (hs : old (pullback.fst f g p) ∈ (s).smoothLocus)
    (hz : oldU ∈ (pullback.fst f g p).asIdeal) :
    ∃ q : (pullback f' g : Scheme),
      next (pullback.fst f' g q) = old (pullback.fst f g p) ∧
      pullback.snd f' g q = pullback.snd f g p ∧
      tu ∉ (pullback.fst f' g q).asIdeal := by
  let v : (O).toScheme :=
    ⟨p, arithmeticTerminalPairOpen_anyDepth_zero_mem hπ data D hgen m j hj g hk p hs hz⟩
  refine ⟨transfer v, ?_, ?_,
    arithmeticTerminalPairTransfer_punctured hπ data m j hj g v⟩
  · exact congrArg (fun k => k v)
      (arithmeticTerminalPairTransfer_first hπ data m j hj g)
  · exact congrArg (fun k => k v)
      (arithmeticTerminalPairTransfer_second hπ data m j hj g)

end FLT.Mazur.WeierstrassDividedDepth
