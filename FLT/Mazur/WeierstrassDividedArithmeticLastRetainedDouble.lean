/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedTransfer

/-!
# Two actual terminal transfers of an equal retained pair

Both original inputs advance on their incidence domains. The construction
keeps the entire ordered pair of resolved arithmetic morphisms unchanged.
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

local notation "O" => arithmeticLastRetainedPairOpen node data m j hj f
local notation "T" => arithmeticLastRetainedPairTransfer node data m j hj f
local notation "swap" => (pullbackSymmetry g' f).hom
local notation "K" => T ≫ swap
local notation "V" => arithmeticLastRetainedPairOpen node data m j hj g'
local notation "nextT" => arithmeticLastRetainedPairTransfer node data m j hj g'

/-- The second incidence condition is pulled back along the actual first transfer. -/
def arithmeticLastRetainedDoubleOpen : (O).toScheme.Opens := K ⁻¹ᵁ V

local notation "D" => arithmeticLastRetainedDoubleOpen node data m j hj

/-- The ordered terminal pair obtained by transferring both original retained inputs. -/
def arithmeticLastRetainedDoubleTransfer : (D).toScheme ⟶ pullback g' g' :=
  (K ∣_ V) ≫ nextT ≫ (pullbackSymmetry g' g').hom

local notation "transfer" => arithmeticLastRetainedDoubleTransfer node data m j hj

omit [IsNoetherianRing R] in
/-- The first terminal input retains every function of the first original resolved input. -/
@[reassoc] theorem arithmeticLastRetainedDoubleTransfer_first :
    transfer ≫ pullback.fst g' g' ≫ chart 1 =
      (D).ι ≫ (O).ι ≫ pullback.fst f f ≫ chart a := by
  dsimp only [arithmeticLastRetainedDoubleOpen]
  simp only [arithmeticLastRetainedDoubleTransfer, Category.assoc,
    pullbackSymmetry_hom_comp_fst_assoc, arithmeticLastRetainedPairTransfer_second_assoc]
  rw [morphismRestrict_ι_assoc]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_snd_assoc,
    arithmeticLastRetainedPairTransfer_first]

omit [IsNoetherianRing R] in
/-- The second terminal input retains every function of the second original resolved input. -/
@[reassoc] theorem arithmeticLastRetainedDoubleTransfer_second :
    transfer ≫ pullback.snd g' g' ≫ chart 1 =
      (D).ι ≫ (O).ι ≫ pullback.snd f f ≫ chart a := by
  dsimp only [arithmeticLastRetainedDoubleOpen]
  simp only [arithmeticLastRetainedDoubleTransfer, Category.assoc,
    pullbackSymmetry_hom_comp_snd_assoc, arithmeticLastRetainedPairTransfer_first]
  rw [morphismRestrict_ι_assoc]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc,
    arithmeticLastRetainedPairTransfer_second_assoc]

local instance arithmeticLastRetainedDouble_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

local notation "e" => data ⟨j + 1, Nat.lt_succ_of_le hj⟩
local notation "u" => tensorCoord W (π ^ (0 + j)) π (e).b3 (e).b4 (e).b6 Q 2

/-- A smooth horizontal-zero second input enters the second actual incidence domain. -/
theorem arithmeticLastRetainedDoubleOpen_zero_mem
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hm : 2 * (j + 1) ≤ depth)
    (p : (O).toScheme)
    (hs : chart a (pullback.snd f f ((O).ι p)) ∈ (s).smoothLocus)
    (hx : u ∈ (coords (pullback.snd f f ((O).ι p))).asIdeal) : p ∈ D := by
  have he : K ≫ pullback.fst f g' = (O).ι ≫ pullback.snd f f := by
    rw [Category.assoc, pullbackSymmetry_hom_comp_fst,
      arithmeticLastRetainedPairTransfer_second]
  apply arithmeticLastRetainedPairOpen_zero_mem node data m j hj g' hgen hm (K p)
  · change chart a ((K ≫ pullback.fst f g') p) ∈ (s).smoothLocus
    rwa [he]
  · change u ∈ (coords ((K ≫ pullback.fst f g') p)).asIdeal
    rwa [he]

end FLT.Mazur.WeierstrassDividedDepth
