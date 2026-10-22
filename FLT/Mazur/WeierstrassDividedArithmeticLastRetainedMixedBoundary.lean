/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticLastRetainedTransfer
public import FLT.Mazur.WeierstrassDividedArithmeticMixedBoundaryNodalReversed

/-!
# Full mixed outputs after an indexed last-retained transfer

Pull the complete terminal/retained boundary cover back to the actual indexed
incidence source. Its second retained input may have zero horizontal coordinate;
the existing mixed cover then performs the second transfer itself.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option quotPrecheck false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalStructure
  arithmeticTensorAtlasMap globalTensorAtlasObject
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsNoetherianRing R]
  [IsLocalRing R] {W : WeierstrassCurve R} {π : R} {n depth : ℕ}
  (node : SplitNodeDepth W π depth)
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (m j : ℕ) (hj : j + 1 ≤ n) (k : ℕ) (hk : k + 1 ≤ j)
local notation "hπ" => node.uniformizer_ne_zero
local notation "Q" => Quotient R π m
local notation "a" => retainedOlderFormulaIndex (j + 1) j (Nat.lt_succ_self j)
local notation "b" => retainedOlderFormulaIndex (j + 1) k (by omega)
local notation "chart" => arithmeticTensorAtlasMap hπ data m (j + 1) hj
local notation "s" => finiteGlobalArithmeticStructure hπ data (j + 1) hj m
local notation "f" => chart a ≫ s
local notation "g" => chart b ≫ s
local notation "ft" => chart 1 ≫ s
local notation "O" => arithmeticLastRetainedPairOpen node data m j hj g
local notation "T" => arithmeticLastRetainedPairTransfer node data m j hj g
local notation "base" => finiteGlobalStructure hπ data (j + 1) hj
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
variable (hdepth : 2 * (j + 1) ≤ depth) (hnear : depth ≤ k + 2 * (j + 1))
local notation "X" => arithmeticMixedBoundaryNodalLocalSource
  node data m (j + 1) hj k (by omega) hdepth hnear
local notation "inc" => arithmeticMixedBoundaryNodalReversedInclusion
  node data m (j + 1) hj k (by omega) hdepth hnear
local notation "out" => arithmeticMixedBoundaryNodalLocalOutput
  node data m (j + 1) hj k (by omega) hdepth hnear

/-- Actual local-source images on the full indexed incidence scheme. -/
def arithmeticLastRetainedMixedBoundaryChart (c : MixedBoundaryNodalLocalIndex) :
    (O).toScheme.Opens := T ⁻¹ᵁ (inc c).opensRange

local notation "C" => arithmeticLastRetainedMixedBoundaryChart
  node data m j hj k hk hdepth hnear

/-- Recover the entire mixed formula source from its genuine open image. -/
def arithmeticLastRetainedMixedBoundaryLift (c : MixedBoundaryNodalLocalIndex) :
    (C c).toScheme ⟶ X c := (T ∣_ (inc c).opensRange) ≫ (inc c).isoOpensRange.inv

local notation "L" => arithmeticLastRetainedMixedBoundaryLift
  node data m j hj k hk hdepth hnear

/-- Both original inputs survive the lift and the indexed incidence transfer. -/
@[reassoc] theorem arithmeticLastRetainedMixedBoundaryLift_inclusion
    (c : MixedBoundaryNodalLocalIndex) : L c ≫ inc c = (C c).ι ≫ T := by
  rw [arithmeticLastRetainedMixedBoundaryLift, Category.assoc,
    Scheme.Hom.isoOpensRange_inv_comp, morphismRestrict_ι]
  rfl

/-- Each incidence chart has its whole arithmetic quotient output. -/
def arithmeticLastRetainedMixedBoundaryOutput (c : MixedBoundaryNodalLocalIndex) :
    (C c).toScheme ⟶ pullback q t := L c ≫ out c

/-- The entire original first coefficient map is retained by the constructed output. -/
@[reassoc] theorem arithmeticLastRetainedMixedBoundaryOutput_base
    (c : MixedBoundaryNodalLocalIndex) :
    arithmeticLastRetainedMixedBoundaryOutput node data m j hj k hk hdepth hnear c ≫
      pullback.fst q t = (C c).ι ≫ (O).ι ≫ pullback.fst f g ≫ f := by
  rw [arithmeticLastRetainedMixedBoundaryOutput, Category.assoc,
    arithmeticMixedBoundaryNodalReversedOutput_base,
    arithmeticLastRetainedMixedBoundaryLift_inclusion_assoc]
  change (C c).ι ≫ T ≫ pullback.fst ft g ≫ chart 1 ≫ s = _
  rw [arithmeticLastRetainedPairTransfer_first_assoc]

local instance arithmeticLastRetainedMixedBoundary_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data (j + 1) hj m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- No puncture on the other retained input is required for full incidence coverage. -/
theorem arithmeticLastRetainedMixedBoundaryChart_covers
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) (hk0 : 0 < k) (p : (O).toScheme)
    (hs : chart a (pullback.fst f g ((O).ι p)) ∈ (s).smoothLocus)
    (ht : chart b (pullback.snd f g ((O).ι p)) ∈ (s).smoothLocus) :
    ∃ c, p ∈ C c := by
  have hfirst : chart 1 (pullback.fst ft g (T p)) ∈ (s).smoothLocus := by
    change (T ≫ pullback.fst ft g ≫ chart 1) p ∈ (s).smoothLocus
    rw [arithmeticLastRetainedPairTransfer_first]
    exact hs
  have hsecond : chart b (pullback.snd ft g (T p)) ∈ (s).smoothLocus := by
    change chart b ((T ≫ pullback.snd ft g) p) ∈ (s).smoothLocus
    rw [arithmeticLastRetainedPairTransfer_second]
    exact ht
  obtain ⟨c, z, hz⟩ := arithmeticMixedBoundaryNodalReversedLocal_exists
    node data m (j + 1) hj k (by omega) hdepth hnear hgen hk0 (T p) hfirst hsecond
  exact ⟨c, z, hz⟩

end FLT.Mazur.WeierstrassDividedDepth
