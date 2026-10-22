/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedZeroOddLocalCover
public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedSelfMixed

/-!
# Creation-zero mixed outputs after one last-retained transfer

Pull the three complete mixed outputs back to the genuine incidence source of
an equal-retained pair. Smooth original inputs reach one of these sources.
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
local notation "K" => T ≫ (pullbackSymmetry g' f).hom
variable (hodd : depth = 2 * (j + 1) + 1)
local notation "X" => arithmeticLastRetainedZeroOddLocalSource node data m j hj hodd
local notation "inc" => arithmeticLastRetainedZeroOddLocalInclusion node data m j hj hodd
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

/-- Each mixed source image pulls back to an actual open of the incidence domain. -/
def arithmeticLastRetainedZeroSelfOddMixedChart
    (b : LastRetainedZeroOddLocalIndex) : (O).toScheme.Opens :=
  K ⁻¹ᵁ (inc b).opensRange

local notation "C" => arithmeticLastRetainedZeroSelfOddMixedChart node data m j hj hodd

/-- Recover the complete mixed formula source from its open image. -/
def arithmeticLastRetainedZeroSelfOddMixedLift
    (b : LastRetainedZeroOddLocalIndex) : (C b).toScheme ⟶ X b :=
  (K ∣_ (inc b).opensRange) ≫ (inc b).isoOpensRange.inv

local notation "lift" => arithmeticLastRetainedZeroSelfOddMixedLift node data m j hj hodd

/-- The recovered source preserves the entire transferred pair. -/
@[reassoc] theorem arithmeticLastRetainedZeroSelfOddMixedLift_inclusion
    (b : LastRetainedZeroOddLocalIndex) :
    lift b ≫ inc b = (C b).ι ≫ K := by
  rw [arithmeticLastRetainedZeroSelfOddMixedLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- Each pulled-back chart carries the complete quotient-valued mixed formula. -/
def arithmeticLastRetainedZeroSelfOddMixedOutput
    (b : LastRetainedZeroOddLocalIndex) : (C b).toScheme ⟶ pullback q t :=
  lift b ≫ arithmeticLastRetainedZeroOddLocalOutput node data m j hj hodd b

/-- The output retains the original first arithmetic coefficient morphism. -/
@[reassoc] theorem arithmeticLastRetainedZeroSelfOddMixedOutput_base
    (b : LastRetainedZeroOddLocalIndex) :
    arithmeticLastRetainedZeroSelfOddMixedOutput node data m j hj hodd b ≫ pullback.fst q t =
      (C b).ι ≫ (O).ι ≫ pullback.fst f f ≫ f := by
  rw [arithmeticLastRetainedZeroSelfOddMixedOutput, Category.assoc,
    arithmeticLastRetainedZeroOddLocalOutput_base,
    arithmeticLastRetainedZeroSelfOddMixedLift_inclusion_assoc,
    arithmeticLastRetainedSelfMixed_first_assoc, ← pullback.condition]

/-- The same complete arithmetic coefficient map comes from the second original input. -/
@[reassoc] theorem arithmeticLastRetainedZeroSelfOddMixedOutput_base_snd
    (b : LastRetainedZeroOddLocalIndex) :
    arithmeticLastRetainedZeroSelfOddMixedOutput node data m j hj hodd b ≫ pullback.fst q t =
      (C b).ι ≫ (O).ι ≫ pullback.snd f f ≫ f := by
  rw [arithmeticLastRetainedZeroSelfOddMixedOutput_base, pullback.condition]

local instance arithmeticLastRetainedZeroSelfOddMixed_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- The three mixed formulas cover every incidence point with smooth original inputs. -/
theorem arithmeticLastRetainedZeroSelfOddMixedChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hzero : j = 0)
    (p : (O).toScheme)
    (hs : chart a (pullback.fst f f ((O).ι p)) ∈ (s).smoothLocus)
    (ht : chart a (pullback.snd f f ((O).ι p)) ∈ (s).smoothLocus) :
    ∃ b, p ∈ C b := by
  have hfirst : chart a (pullback.fst f g' (K p)) ∈ (s).smoothLocus := by
    change chart a ((K ≫ pullback.fst f g') p) ∈ (s).smoothLocus
    rw [arithmeticLastRetainedSelfMixed_first]
    exact ht
  have hsecond : chart 1 (pullback.snd f g' (K p)) ∈ (s).smoothLocus := by
    change (K ≫ pullback.snd f g' ≫ chart 1) p ∈ (s).smoothLocus
    rw [arithmeticLastRetainedSelfMixed_second]
    exact hs
  obtain ⟨b, z, hz⟩ := arithmeticLastRetainedZeroOddLocal_exists
    node data m j hj hodd hgen hzero (K p) hfirst hsecond
  exact ⟨b, z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth
