/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineSubgroupScheme

/-!
# Constructed comparison charts on the actual normalized chart products

Use the canonical affine open cover of each ordered product of normalized
characteristic charts. Every such open now has its actual varying full curve
comparison scheme and closed subgroup-preserving scheme.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (b c : Bool)

/-- The actual ordered product of the two normalized characteristic charts. -/
def normalizedProduct : Scheme := (normalizedLocus n b) ⨯ (normalizedLocus n c)

/-- The coordinate ring of a canonical affine open in the actual product. -/
abbrev ProductChartRing (i : (normalizedProduct n b c).affineCover.I₀) :=
  Γ((normalizedProduct n b c).affineCover.X i, ⊤)

/-- The canonical spectrum chart maps into the original product. -/
def productChartMap (i : (normalizedProduct n b c).affineCover.I₀) :
    Spec (ProductChartRing n b c i) ⟶ normalizedProduct n b c :=
  ((normalizedProduct n b c).affineCover.X i).isoSpec.inv ≫
    (normalizedProduct n b c).affineCover.f i

/-- These actual spectrum charts cover every point of the original product. -/
theorem productChartMap_covers (x : normalizedProduct n b c) :
    ∃ i y, productChartMap n b c i y = x := by
  obtain ⟨y, hy⟩ := (normalizedProduct n b c).affineCover.covers x
  refine ⟨(normalizedProduct n b c).affineCover.idx x,
    (((normalizedProduct n b c).affineCover.X _).isoSpec.hom) y, ?_⟩
  change (((normalizedProduct n b c).affineCover.X _).isoSpec.hom ≫
    ((normalizedProduct n b c).affineCover.X _).isoSpec.inv ≫
      (normalizedProduct n b c).affineCover.f _) y = x
  simpa only [Iso.hom_inv_id_assoc] using hy

/-- Every canonical product chart has its constructed full subgroup comparison scheme. -/
def productSubgroupComparisonChart (i : (normalizedProduct n b c).affineCover.I₀) : Scheme :=
  affineSubgroupScheme n b c (productChartMap n b c i ≫ prod.fst)
    (productChartMap n b c i ≫ prod.snd)

/-- The comparison chart retains its original map into the normalized product. -/
def productSubgroupComparisonMap (i : (normalizedProduct n b c).affineCover.I₀) :
    productSubgroupComparisonChart n b c i ⟶ normalizedProduct n b c :=
  affineSubgroupStructure n b c (productChartMap n b c i ≫ prod.fst)
    (productChartMap n b c i ≫ prod.snd) ≫ productChartMap n b c i

end FLT.Mazur.CyclicCharacteristicAtlas
