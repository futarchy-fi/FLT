/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedArithmeticRetainedZeroShortLocalCover

/-!
# The short-atlas five-chart cover of the smooth creation-zero pair

Restrict the constructed local sources to the smooth input pair. Their maps
form an open cover, and their quotient-valued outputs preserve the original
pair's coefficient map. Compatibility of these outputs is a separate question.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
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
local notation "Q" => Quotient R π m
local notation "c" => (Fin.succ ⟨k - i,
  Nat.lt_succ_of_le ((Nat.sub_le k i).trans (Nat.le_succ k))⟩ : Fin (k + 3))
local notation "chart" => arithmeticTensorAtlasMap hπ data m k hk
local notation "s" => finiteGlobalArithmeticStructure hπ data k hk m
local notation "fa" => chart c ≫ s
local notation "inc" => arithmeticRetainedZeroShortLocalInclusion node data m k hk
  i hi hsum hpre
local notation "out" => arithmeticRetainedZeroShortLocalOutput node data m k hk i hi hsum hpre
local notation "base" => finiteGlobalStructure hπ data k hk
local notation "t" => (base).smoothLocus.ι ≫ base
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))

local instance arithmeticZeroShortSmoothCover_structure (h : π ≠ 0) :
    LocallyOfFinitePresentation (finiteGlobalArithmeticStructure h data k hk m) := by
  unfold finiteGlobalArithmeticStructure
  infer_instance

/-- Both full original inputs are required to lie in the relative smooth locus. -/
def arithmeticRetainedZeroShortSmoothPairOpen : (pullback fa fa).Opens :=
  (pullback.fst fa fa ≫ chart c) ⁻¹ᵁ (s).smoothLocus ⊓
    (pullback.snd fa fa ≫ chart c) ⁻¹ᵁ (s).smoothLocus

local notation "U" => arithmeticRetainedZeroShortSmoothPairOpen node data m k hk i

/-- The actual smooth input restriction of each formula source. -/
def arithmeticRetainedZeroShortSmoothLocalSource (b : RetainedZeroShortLocalIndex) : Scheme :=
  (inc b ⁻¹ᵁ U).toScheme

/-- Restricting the actual source inclusion retains its original target pair. -/
def arithmeticRetainedZeroShortSmoothLocalInclusion (b : RetainedZeroShortLocalIndex) :
    arithmeticRetainedZeroShortSmoothLocalSource node data m k hk i hi hsum hpre b ⟶
      (U).toScheme := inc b ∣_ U

local notation "map" => arithmeticRetainedZeroShortSmoothLocalInclusion
  node data m k hk i hi hsum hpre

/-- The restricted formula source still maps by an open immersion. -/
instance arithmeticRetainedZeroShortSmoothLocalInclusion_isOpenImmersion
    (b : RetainedZeroShortLocalIndex) :
    IsOpenImmersion (map b) := by
  unfold arithmeticRetainedZeroShortSmoothLocalInclusion
  infer_instance

/-- The five original formula sources form a genuine open cover of the smooth pair. -/
def arithmeticRetainedZeroShortSmoothCover (hz : i = 0)
    (hgen : IsLocalRing.maximalIdeal R = ideal R π) : (U).toScheme.OpenCover where
  I₀ := RetainedZeroShortLocalIndex
  X := arithmeticRetainedZeroShortSmoothLocalSource node data m k hk i hi hsum hpre
  f := map
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro p
    obtain ⟨b, z, hb⟩ := arithmeticRetainedZeroShortLocal_exists node data m k hk
      i hi hsum hpre hz hgen p.1 p.2.1 p.2.2
    have hz' : z ∈ inc b ⁻¹ᵁ U := by
      change inc b z ∈ U
      rw [hb]
      exact p.2
    refine ⟨b, ⟨z, hz'⟩, ?_⟩
    apply Subtype.ext
    exact (morphismRestrict_base_coe (inc b) U ⟨z, hz'⟩).trans hb

/-- The cover's local sums keep the original full quotient-valued formula. -/
def arithmeticRetainedZeroShortSmoothLocalOutput (b : RetainedZeroShortLocalIndex) :
    arithmeticRetainedZeroShortSmoothLocalSource node data m k hk i hi hsum hpre b ⟶
      pullback q t := (inc b ⁻¹ᵁ U).ι ≫ out b

/-- Every restricted output retains the smooth original pair's coefficient point. -/
@[reassoc] theorem arithmeticRetainedZeroShortSmoothLocalOutput_base
    (b : RetainedZeroShortLocalIndex) :
    arithmeticRetainedZeroShortSmoothLocalOutput node data m k hk i hi hsum hpre b ≫
      pullback.fst q t = map b ≫ (U).ι ≫ pullback.fst fa fa ≫ fa := by
  rw [arithmeticRetainedZeroShortSmoothLocalOutput, Category.assoc,
    arithmeticRetainedZeroShortLocalOutput_base, arithmeticRetainedZeroShortSmoothLocalInclusion,
    morphismRestrict_ι_assoc]

end FLT.Mazur.WeierstrassDividedDepth
