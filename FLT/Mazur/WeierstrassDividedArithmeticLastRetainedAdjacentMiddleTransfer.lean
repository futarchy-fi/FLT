/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSelfSmoothCover
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPairCoverage

/-!
# Full middle self outputs after the earlier adjacent input advances

Pull the full last-retained self cover back to the earlier incidence domain.
Both original input morphisms survive, with no puncture on the second input.
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
  (m i : ℕ) (hk : i + 3 ≤ n) (hmiddle : 2 * (i + 3) = depth)
local notation "k" => i + 3
local notation "j" => i + 1
local notation "hj" => (by omega : j + 2 ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "a" => (Fin.succ ⟨k - j,
  Nat.lt_succ_of_le ((Nat.sub_le k j).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "c" => (Fin.succ ⟨k - (j + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (j + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart a ≫ s
local notation "g" => chart c ≫ s
local notation "D" => arithmeticFixedAdjacentPairOpen hπ data m k hk j hj g
local notation "T" => arithmeticFixedAdjacentPairTransfer hπ data m k hk j hj g
local notation "X" => arithmeticLastRetainedSelfLocalSource node data m (i + 1) hk hmiddle
local notation "inc" => arithmeticLastRetainedSelfLocalInclusion node data m (i + 1) hk hmiddle
local notation "out" => arithmeticLastRetainedSelfLocalOutput node data m (i + 1) hk hmiddle
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R (Quotient R π m)))

/-- Actual self-source images pulled back to the whole adjacent incidence scheme. -/
def arithmeticLastRetainedAdjacentMiddleTransferChart (b : LastRetainedSelfLocalIndex) :
    (D).toScheme.Opens := T ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedAdjacentMiddleTransferChart node data m i hk hmiddle

/-- Recover the whole self-source from its image. -/
def arithmeticLastRetainedAdjacentMiddleTransferLift (b : LastRetainedSelfLocalIndex) :
    (C b).toScheme ⟶ X b := (T ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "L" => arithmeticLastRetainedAdjacentMiddleTransferLift node data m i hk hmiddle

/-- The lift preserves the complete self-pair after transfer. -/
@[reassoc] theorem arithmeticLastRetainedAdjacentMiddleTransferLift_inclusion
    (b : LastRetainedSelfLocalIndex) : L b ≫ inc b = (C b).ι ≫ T := by
  rw [arithmeticLastRetainedAdjacentMiddleTransferLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- Every pulled-back self source carries its full arithmetic quotient output. -/
def arithmeticLastRetainedAdjacentMiddleTransferOutput (b : LastRetainedSelfLocalIndex) :
    (C b).toScheme ⟶ pullback q t := L b ≫ out b

/-- The whole first original coefficient morphism is preserved. -/
@[reassoc] theorem arithmeticLastRetainedAdjacentMiddleTransferOutput_base
    (b : LastRetainedSelfLocalIndex) :
    arithmeticLastRetainedAdjacentMiddleTransferOutput node data m i hk hmiddle b ≫
      pullback.fst q t =
      (C b).ι ≫ (D).ι ≫ pullback.fst f g ≫ f := by
  rw [arithmeticLastRetainedAdjacentMiddleTransferOutput, Category.assoc,
    arithmeticLastRetainedSelfLocalOutput_base]
  change L b ≫ inc b ≫ pullback.fst g g ≫ g = _
  rw [arithmeticLastRetainedAdjacentMiddleTransferLift_inclusion_assoc,
    arithmeticFixedAdjacentPairTransfer_first_assoc]

local instance arithmeticLastRetainedAdjacentMiddleTransfer_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Every smooth incidence point reaches a full self-output domain. -/
theorem arithmeticLastRetainedAdjacentMiddleTransferChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (p : (D).toScheme)
    (hs : chart a (pullback.fst f g ((D).ι p)) ∈ (s).smoothLocus)
    (ht : chart c (pullback.snd f g ((D).ι p)) ∈ (s).smoothLocus) :
    ∃ b, p ∈ C b := by
  have hs' : chart c (pullback.fst g g (T p)) ∈ (s).smoothLocus := by
    change (T ≫ pullback.fst g g ≫ chart c) p ∈ (s).smoothLocus
    rw [arithmeticFixedAdjacentPairTransfer_first]
    exact hs
  have ht' : chart c (pullback.snd g g (T p)) ∈ (s).smoothLocus := by
    change chart c ((T ≫ pullback.snd g g) p) ∈ (s).smoothLocus
    rw [arithmeticFixedAdjacentPairTransfer_second]
    exact ht
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedSelfLocal_exists
    node data m (i + 1) hk hmiddle hgen (T p) hs' ht'
  exact ⟨b, z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth
