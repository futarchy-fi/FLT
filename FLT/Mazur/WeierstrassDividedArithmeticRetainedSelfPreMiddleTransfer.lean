/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetSelfPreMiddleAddition
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedDoubleCoverage

/-!
# Actual addition outputs on the whole equal retained incidence domain

Pull the constructed quotient-valued target formulas through the actual
simultaneous chart transfer. The resulting open cover retains every function
on both original inputs, including at creation depth zero. All node depths strictly above twice the
shifted depth are covered; no coefficient normalization is needed.
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
  (hsum : (i + 1) + (i + 1) ≤ k) (hpre : 2 * (i + 1) < depth)
local notation "hπ" => node.uniformizer_ne_zero
local notation "a" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart a ≫ s
local notation "g" => chart c ≫ s
local notation "D" => arithmeticRetainedDoubleOpen hπ data m k hk i i hi hi
local notation "T" => arithmeticRetainedDoubleTransfer hπ data m k hk i i hi hi
local notation "V" => arithmeticTargetSelfPreMiddleOpen node data m k hk i hi hsum hpre
local notation "Z" => arithmeticTargetSelfReciprocalOpen node data m k hk i hi
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "U" => (base).smoothLocus
local notation "t" => (U).ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R (Quotient R π m)))

/-- Two actual formula domains on the unchanged equal-depth incidence source. -/
def arithmeticRetainedSelfPreMiddleTransferChart : Bool → (D).toScheme.Opens
  | false => T ⁻¹ᵁ V
  | true => T ⁻¹ᵁ Z

local notation "C" => arithmeticRetainedSelfPreMiddleTransferChart node data m k hk i hi hsum hpre

/-- Each source chart carries a constructed output over the original quotient. -/
def arithmeticRetainedSelfPreMiddleTransferOutput : (b : Bool) → (C b).toScheme ⟶ pullback q t
  | false => (T ∣_ V) ≫ arithmeticTargetSelfPreMiddleQuotientOutput node data m k hk i hi hsum hpre
  | true => (T ∣_ Z) ≫ arithmeticTargetSelfReciprocalQuotientOutput node data m k hk i hi

local notation "out" => arithmeticRetainedSelfPreMiddleTransferOutput
  node data m k hk i hi hsum hpre

/-- Every chart output retains the original first arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedSelfPreMiddleTransferOutput_base (b : Bool) :
    out b ≫ pullback.fst q t = (C b).ι ≫ (D).ι ≫ pullback.fst f f ≫ f := by
  cases b <;>
    simp only [arithmeticRetainedSelfPreMiddleTransferOutput, Category.assoc,
      arithmeticTargetSelfPreMiddleQuotientOutput_base,
      arithmeticTargetSelfReciprocalQuotientOutput_base, morphismRestrict_ι_assoc]
  · exact congrArg (fun z => (C false).ι ≫ z)
      (arithmeticRetainedDoubleTransfer_first_assoc hπ data m k hk i i hi hi s)
  · exact congrArg (fun z => (C true).ι ≫ z)
      (arithmeticRetainedDoubleTransfer_first_assoc hπ data m k hk i i hi hi s)

/-- The same output retains the second original arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticRetainedSelfPreMiddleTransferOutput_base_snd (b : Bool) :
    out b ≫ pullback.fst q t = (C b).ι ≫ (D).ι ≫ pullback.snd f f ≫ f := by
  rw [arithmeticRetainedSelfPreMiddleTransferOutput_base, pullback.condition]

/-- The actual incidence transfer is covered without any coordinate puncture premise. -/
theorem arithmeticRetainedSelfPreMiddleTransferChart_covers :
    (⨆ b, C b) = ⊤ := by
  apply top_unique
  intro p _
  have hp := arithmeticRetainedDoubleTransfer_punctured hπ data m k hk i i hi hi p
  rcases arithmeticTargetSelfPreMiddle_punctured_cover node data m k hk i hi hsum hpre
    (T p) hp.1 hp.2 with hv | hz
  · exact (le_iSup (fun b => C b) false) hv
  · exact (le_iSup (fun b => C b) true) hz

/-- A genuine open cover with quotient-valued outputs on the entire incidence domain. -/
def arithmeticRetainedSelfPreMiddleTransferCover :
    (D).toScheme.OpenCover :=
  (D).toScheme.openCoverOfIsOpenCover C
    (arithmeticRetainedSelfPreMiddleTransferChart_covers node data m k hk i hi hsum hpre)

end FLT.Mazur.WeierstrassDividedDepth
