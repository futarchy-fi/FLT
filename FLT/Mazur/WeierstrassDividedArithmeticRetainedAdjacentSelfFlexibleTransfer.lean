/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetSelfFlexiblePreMiddle
public import FLT.Mazur.WeierstrassDividedArithmeticFixedAdjacentPairCoverage

/-!
# Flexible self outputs after the first adjacent input advances

Pull the two genuine self-pair formulas back along a single adjacent transfer.
These outputs cover the actual incidence source when the unchanged input is
punctured. Both original coefficient morphisms are preserved.
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
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k)
  (hstage : min (2 * (i + 1)) (depth - 2 * (i + 1)) ≤ k) (hpre : 2 * (i + 1) < depth)
local notation "hπ" => node.uniformizer_ne_zero
local notation "a" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart a ≫ s
local notation "g" => chart c ≫ s
local notation "D" => arithmeticFixedAdjacentPairOpen hπ data m k hk i hi g
local notation "T" => arithmeticFixedAdjacentPairTransfer hπ data m k hk i hi g
local notation "V" => arithmeticTargetSelfFlexiblePreMiddleOpen node data m k hk i hi hstage hpre
local notation "Z" => arithmeticTargetSelfReciprocalOpen node data m k hk i hi
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R (Quotient R π m)))

/-- Two actual formula domains on the unchanged equal-depth incidence source. -/
def arithmeticRetainedAdjacentSelfFlexibleTransferChart : Bool → (D).toScheme.Opens
  | false => T ⁻¹ᵁ V
  | true => T ⁻¹ᵁ Z

local notation "C" => arithmeticRetainedAdjacentSelfFlexibleTransferChart
  node data m k hk i hi hstage hpre

/-- Each source chart carries a constructed output over the original quotient. -/
def arithmeticRetainedAdjacentSelfFlexibleTransferOutput :
    (b : Bool) → (C b).toScheme ⟶ pullback q t
  | false => (T ∣_ V) ≫ arithmeticTargetSelfFlexiblePreMiddleQuotientOutput
      node data m k hk i hi hstage hpre
  | true => (T ∣_ Z) ≫ arithmeticTargetSelfReciprocalQuotientOutput node data m k hk i hi

local notation "out" => arithmeticRetainedAdjacentSelfFlexibleTransferOutput
  node data m k hk i hi hstage hpre

/-- Every chart output retains the original first arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedAdjacentSelfFlexibleTransferOutput_base (b : Bool) :
    out b ≫ pullback.fst q t = (C b).ι ≫ (D).ι ≫ pullback.fst f g ≫ f := by
  cases b <;>
    simp only [arithmeticRetainedAdjacentSelfFlexibleTransferOutput, Category.assoc,
      arithmeticTargetSelfFlexiblePreMiddleQuotientOutput_base,
      arithmeticTargetSelfReciprocalQuotientOutput_base, morphismRestrict_ι_assoc]
  · exact congrArg (fun z => (C false).ι ≫ z)
      (arithmeticFixedAdjacentPairTransfer_first_assoc hπ data m k hk i hi g s)
  · exact congrArg (fun z => (C true).ι ≫ z)
      (arithmeticFixedAdjacentPairTransfer_first_assoc hπ data m k hk i hi g s)

/-- The same output retains the second original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedAdjacentSelfFlexibleTransferOutput_base_snd (b : Bool) :
    out b ≫ pullback.fst q t = (C b).ι ≫ (D).ι ≫ pullback.snd f g ≫ g := by
  rw [arithmeticRetainedAdjacentSelfFlexibleTransferOutput_base, pullback.condition]

local notation "Q" => Quotient R π m
local notation "e" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2

/-- Puncturing the unchanged input covers the whole single-transfer incidence point. -/
theorem arithmeticRetainedAdjacentSelfFlexibleTransferChart_covers (z : (D).toScheme)
    (hu : u ∉ (I (pullback.snd f g ((D).ι z))).asIdeal) : ∃ b, z ∈ C b := by
  have hx := arithmeticFixedAdjacentPairTransfer_punctured hπ data m k hk i hi g z
  have hy : u ∉ (I (pullback.snd g g (T z))).asIdeal := by
    have he := congrArg (fun morphism => morphism z)
      (arithmeticFixedAdjacentPairTransfer_second hπ data m k hk i hi g)
    change pullback.snd g g (T z) = pullback.snd f g ((D).ι z) at he
    rw [he]
    exact hu
  rcases arithmeticTargetSelfFlexiblePreMiddle_punctured_cover node data m k hk i hi
    hstage hpre (T z) hx hy with hv | hz
  · exact ⟨false, hv⟩
  · exact ⟨true, hz⟩

end FLT.Mazur.WeierstrassDividedDepth
