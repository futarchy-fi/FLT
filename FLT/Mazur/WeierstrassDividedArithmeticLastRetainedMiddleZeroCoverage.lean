/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedMiddleOutput
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedDoubleMiddleOutput

/-!
# Coverage of horizontal-zero inputs at the shifted middle boundary

The actual smooth single and double incidence sources cover the corresponding
zero-coordinate strata. Their quotient outputs were constructed separately.
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



local instance arithmeticLastRetainedMiddleZero_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "u" => tensorCoord W (π ^ (0 + j)) π (e).b3 (e).b4 (e).b6 Q 2
local notation "A" => tensorIntegralAtlasSmoothOpen hπ data Q (j + 1) hj
local notation "O" => arithmeticLastRetainedPairOpen node data m j hj g'
local notation "D" => arithmeticLastRetainedMiddleSmoothOpen node data m j hj

/-- Every smooth zero/terminal pair belongs to the actual middle output source. -/
theorem arithmeticLastRetainedMiddleSmoothOpen_zero_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hm : 2 * (j + 1) = depth)
    (p : (pullback f g' : Scheme))
    (hs : chart a (pullback.fst f g' p) ∈ (s).smoothLocus)
    (ht : chart 1 (pullback.snd f g' p) ∈ (s).smoothLocus)
    (hx : u ∈ (coords (pullback.fst f g' p)).asIdeal) :
    ∃ z : (D).toScheme, ((D).ι ≫ (O).ι) z = p := by
  let v : (O).toScheme := ⟨p,
    arithmeticLastRetainedPairOpen_zero_mem node data m j hj g' hgen hm.le p hs hx⟩
  have hv : v ∈ D := by
    constructor
    · exact (arithmeticAtlasSmoothOpen_mem_relative hπ data m (j + 1) hj a _).mpr hs
    · exact (arithmeticAtlasSmoothOpen_mem_relative hπ data m (j + 1) hj 1 _).mpr ht
  exact ⟨⟨v, hv⟩, rfl⟩

local notation "O₀" => arithmeticLastRetainedPairOpen node data m j hj f
local notation "O₂" => arithmeticLastRetainedDoubleOpen node data m j hj
local notation "D₂" => arithmeticLastRetainedDoubleMiddleSmoothOpen node data m j hj

/-- Every smooth double-zero pair lies in the genuine double-transfer output source. -/
theorem arithmeticLastRetainedDoubleMiddleSmoothOpen_zero_exists
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hm : 2 * (j + 1) = depth)
    (p : (pullback f f : Scheme))
    (hs : chart a (pullback.fst f f p) ∈ (s).smoothLocus)
    (ht : chart a (pullback.snd f f p) ∈ (s).smoothLocus)
    (hx : u ∈ (coords (pullback.fst f f p)).asIdeal)
    (hy : u ∈ (coords (pullback.snd f f p)).asIdeal) :
    ∃ z : (D₂).toScheme, ((D₂).ι ≫ (O₂).ι ≫ (O₀).ι) z = p := by
  let v : (O₀).toScheme := ⟨p,
    arithmeticLastRetainedPairOpen_zero_mem node data m j hj f hgen hm.le p hs hx⟩
  let w : (O₂).toScheme := ⟨v,
    arithmeticLastRetainedDoubleOpen_zero_mem node data m j hj hgen hm.le v ht hy⟩
  have hw : w ∈ D₂ := by
    constructor
    · exact (arithmeticAtlasSmoothOpen_mem_relative hπ data m (j + 1) hj a _).mpr hs
    · exact (arithmeticAtlasSmoothOpen_mem_relative hπ data m (j + 1) hj a _).mpr ht
  exact ⟨⟨w, hw⟩, rfl⟩

end FLT.Mazur.WeierstrassDividedDepth
