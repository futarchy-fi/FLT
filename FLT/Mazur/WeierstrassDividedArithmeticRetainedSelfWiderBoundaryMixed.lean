/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticTargetWiderBoundaryQuotientOutput
public import FLT.Mazur.WeierstrassDividedArithmeticRetainedSecondAdditionCoverage
public import FLT.Mazur.WeierstrassDividedArithmeticAdjacentCoordinateShift

/-!
# Reflected additions after one equal-depth retained transfer

The first original input advances once and the second is kept in full. The
three genuine unequal-depth outputs are pulled back to the actual incidence
source; their coefficient morphisms are those of the original pair.
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
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m k : ℕ) (hk : k ≤ n) (i : ℕ) (hi : i + 2 ≤ k) (hiNext : (i + 1) + 2 ≤ k)
  (hlo : (i + 1) + 2 * (i + 2) ≤ depth) (hhi : depth ≤ 2 * ((i + 1) + (i + 2)))
  (hstage : depth - (i + 1) - (i + 2) ≤ k)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "e" => data ⟨i + 2, Nat.lt_succ_of_le (hi.trans hk)⟩
local notation "c" => (Fin.succ ⟨k - (i + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k (i + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "d" => (Fin.succ ⟨k - ((i + 1) + 1),
  Nat.lt_succ_of_le ((Nat.sub_le k ((i + 1) + 1)).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "f" => chart c ≫ s
local notation "g" => chart d ≫ s
local notation "I" => arithmeticFixedAdjacentTargetCoordinates hπ data m k hk i hi
local notation "u" => tensorCoord W (π ^ (0 + (i + 1))) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) Q 2
local notation "O" => arithmeticFixedAdjacentPairOpen hπ data m k hk (i + 1) hiNext f
local notation "T" => arithmeticFixedAdjacentPairTransfer hπ data m k hk (i + 1) hiNext f
local notation "K" => T ≫ (pullbackSymmetry g f).hom
local notation "V" => arithmeticTargetWiderBoundaryOutputChart node data m k hk i (i + 1)
  hi hiNext (by omega) (by omega) (by omega) (by omega)
local notation "out" => arithmeticTargetWiderBoundaryQuotientOutput node data m k hk i (i + 1)
  hi hiNext (by omega) (by omega) (by omega) (by omega)
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Three actual local output domains on the single-transfer incidence source. -/
def arithmeticRetainedSelfWiderBoundaryMixedChart (b : Fin 3) : (O).toScheme.Opens := K ⁻¹ᵁ V b

local notation "C" => arithmeticRetainedSelfWiderBoundaryMixedChart node data m k hk i hi hiNext
  hlo hhi hstage

/-- Each formula is an actual morphism over the unchanged arithmetic quotient. -/
def arithmeticRetainedSelfWiderBoundaryMixedOutput (b : Fin 3) : (C b).toScheme ⟶ pullback q t :=
  (K ∣_ V b) ≫ out b

/-- The pulled-back output preserves the first original arithmetic coefficient point. -/
@[reassoc] theorem arithmeticRetainedSelfWiderBoundaryMixedOutput_base (b : Fin 3) :
    arithmeticRetainedSelfWiderBoundaryMixedOutput node data m k hk i hi hiNext hlo hhi hstage b ≫
      pullback.fst q t = (C b).ι ≫ (O).ι ≫ pullback.fst f f ≫ f := by
  rw [arithmeticRetainedSelfWiderBoundaryMixedOutput, Category.assoc,
    arithmeticTargetWiderBoundaryQuotientOutput_base, morphismRestrict_ι_assoc]
  simp only [Category.assoc, pullbackSymmetry_hom_comp_fst_assoc]
  rw [arithmeticFixedAdjacentPairTransfer_second_assoc, ← pullback.condition]
  rfl

/-- The second original coefficient point is also preserved on every chart. -/
@[reassoc] theorem arithmeticRetainedSelfWiderBoundaryMixedOutput_base_snd (b : Fin 3) :
    arithmeticRetainedSelfWiderBoundaryMixedOutput node data m k hk i hi hiNext hlo hhi hstage b ≫
      pullback.fst q t = (C b).ι ≫ (O).ι ≫ pullback.snd f f ≫ f := by
  rw [arithmeticRetainedSelfWiderBoundaryMixedOutput_base, pullback.condition]

/-- The unchanged input's puncture covers the whole actual single-transfer source. -/
theorem arithmeticRetainedSelfWiderBoundaryMixedChart_covers (p : (O).toScheme)
    (hu : u ∉ (I (pullback.snd f f ((O).ι p))).asIdeal) : ∃ b, p ∈ C b := by
  apply arithmeticTargetWiderBoundaryOutputChart_punctured node data m k hk i (i + 1) hi hiNext
    (by omega) (by omega) (by omega) (by omega) (by omega) (K p)
  · change u ∉ (I (pullback.fst f g ((pullbackSymmetry g f).hom (T p)))).asIdeal
    rw [SchemePairSymmetryPoints.fst_apply]
    have he := congrArg (fun z => z p)
      (arithmeticFixedAdjacentPairTransfer_second hπ data m k hk (i + 1) hiNext f)
    change pullback.snd g f (T p) = pullback.snd f f ((O).ι p) at he
    rw [he]
    exact hu
  · have hp := arithmeticFixedAdjacentPairTransfer_punctured
      hπ data m k hk (i + 1) hiNext f p
    simpa only [Scheme.Hom.comp_apply, SchemePairSymmetryPoints.snd_apply] using hp

end FLT.Mazur.WeierstrassDividedDepth
