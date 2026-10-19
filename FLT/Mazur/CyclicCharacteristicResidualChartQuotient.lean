/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbitChartTopology

/-!
# The residual quotient on each actual finite characteristic quotient

The existing finite quotient surjects onto the full characteristic orbit open
with its quotient topology. Its remaining fibers are exactly the images of
points of the full same-chart comparison scheme, including residual arrows.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace Topology
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The original finite quotient maps into its exact characteristic orbit open. -/
def finiteToIntegerOpen (b : Bool) :
    (normalizedQuotient n b).toTopCat ⟶ (Opens.toTopCat (space n)).obj
      (integerOpen n (chartInteger b)) :=
  TopCat.ofHom ⟨fun y => ⟨finiteProjection n b y,
    (Set.ext_iff.mp (finiteProjection_range n b) _).mp ⟨y, rfl⟩⟩,
    (finiteProjection_continuous n b).subtype_mk _⟩

/-- The factorization preserves the actual normalized parameter projection. -/
theorem normalizedQuotientMap_finiteToIntegerOpen (b : Bool) :
    (normalizedQuotientMap n b).base ≫ finiteToIntegerOpen n b = chartToIntegerOpen n b := by
  ext x
  exact Subtype.ext (finiteProjection_apply n b x)

/-- The residual map has the actual quotient topology, not merely a continuous surjection. -/
theorem finiteToIntegerOpen_isQuotientMap (b : Bool) :
    IsQuotientMap (finiteToIntegerOpen n b) := by
  apply IsQuotientMap.of_comp (normalizedQuotientMap n b).continuous
    (finiteToIntegerOpen n b).hom.continuous
  have he : finiteToIntegerOpen n b ∘ normalizedQuotientMap n b = chartToIntegerOpen n b :=
    funext (fun x => Subtype.ext (finiteProjection_apply n b x))
  rw [he]
  exact chartToIntegerOpen_isQuotientMap n b

/-- Full orbit equality on fixed chart components is witnessed by their actual arrow scheme. -/
theorem chartProjection_eq_iff (b c : Bool) (x : normalizedLocus n b)
    (y : normalizedLocus n c) :
    chartProjection n b x = chartProjection n c y ↔
      ∃ a : productSubgroupScheme n b c,
        productArrowSource n b c a = x ∧ productArrowTarget n b c a = y := by
  change projection n (normalizedDisjointInclusion n b x) =
    projection n (normalizedDisjointInclusion n c y) ↔ _
  rw [projection_eq_iff]
  constructor
  · rintro ⟨a, ha, ht⟩
    obtain ⟨⟨d, e⟩, t, rfl⟩ :=
      (sigmaOpenCover (fun p : Bool × Bool => productSubgroupScheme n p.1 p.2)).exists_eq a
    change (disjointComparisonInclusion n d e ≫ disjointComparisonSource n) t = _ at ha
    change (disjointComparisonInclusion n d e ≫ disjointComparisonTarget n) t = _ at ht
    rw [disjointComparisonInclusion_source, Scheme.Hom.comp_apply] at ha
    rw [disjointComparisonInclusion_target, Scheme.Hom.comp_apply] at ht
    have hd : d = b := congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp ha)
    have he : e = c := congrArg Sigma.fst ((sigmaι_eq_iff _ _ _ _ _).mp ht)
    subst d
    subst e
    exact ⟨t, (normalizedDisjointInclusion n b).isOpenEmbedding.injective ha,
      (normalizedDisjointInclusion n c).isOpenEmbedding.injective ht⟩
  · rintro ⟨a, ha, ht⟩
    refine ⟨disjointComparisonInclusion n b c a, ?_, ?_⟩
    · change (disjointComparisonInclusion n b c ≫ disjointComparisonSource n) a = _
      rw [disjointComparisonInclusion_source, Scheme.Hom.comp_apply, ha]
    · change (disjointComparisonInclusion n b c ≫ disjointComparisonTarget n) a = _
      rw [disjointComparisonInclusion_target, Scheme.Hom.comp_apply, ht]

/-- The residual fibers of the finite quotient retain exactly the full same-chart arrows. -/
theorem finiteProjection_eq_iff (b : Bool) (y z : normalizedQuotient n b) :
    finiteProjection n b y = finiteProjection n b z ↔
      ∃ a : productSubgroupScheme n b b,
        normalizedQuotientMap n b (productArrowSource n b b a) = y ∧
          normalizedQuotientMap n b (productArrowTarget n b b a) = z := by
  obtain ⟨x, rfl⟩ := (normalizedQuotientMap n b).surjective y
  obtain ⟨w, rfl⟩ := (normalizedQuotientMap n b).surjective z
  rw [finiteProjection_apply, finiteProjection_apply]
  change chartProjection n b x = chartProjection n b w ↔ _
  constructor
  · intro h
    obtain ⟨a, ha, ht⟩ := (chartProjection_eq_iff n b b x w).mp h
    exact ⟨a, congrArg (normalizedQuotientMap n b) ha,
      congrArg (normalizedQuotientMap n b) ht⟩
  · rintro ⟨a, ha, ht⟩
    have hs := projection_eq_of_finite_quotient_eq n b _ _ ha
    have hr := projection_eq_of_finite_quotient_eq n b _ _ ht
    exact hs.symm.trans (((chartProjection_eq_iff n b b _ _).mpr ⟨a, rfl, rfl⟩).trans hr)

end FLT.Mazur.CyclicCharacteristicOrbit
