/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationMixedResidualPieces
public import FLT.Mazur.EquivalenceRelationMixedChartProjections

/-!
# Independent embedding branches are actual source opens

Every nonresidual piece of an independently restricted mixed relation is
isomorphic to the first source open intersected with the inverse image of the
second open under its specified subframe map. These are source restrictions
with exact scheme maps, including all nilpotents.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J : Type} [Fintype I] [Fintype J] (o : I) (o' : J)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens) (ι : J ↪ I)
local notation "M" => mixedChartOpen o o' U V
local notation "g" => subframeGraph e o o' ι

/-- The actual source domain of the restricted embedding graph. -/
def mixedEmbeddingDomain : (source p q I o).Opens := (g) ⁻¹ᵁ M

omit [Etale p] in
/-- Its formula retains both independent chart domains and the specified label embedding. -/
theorem mixedEmbeddingDomain_eq :
    mixedEmbeddingDomain e o o' U V ι = U ⊓ subframeMap e o o' ι ⁻¹ᵁ V := by
  simp only [mixedEmbeddingDomain, mixedChartOpen, Scheme.Hom.preimage_inf,
    ← Scheme.Hom.comp_preimage, subframeGraph_fst, subframeGraph_snd,
    Scheme.Hom.id_preimage]

/-- The unchanged graph restricted to both independent chart domains. -/
def mixedEmbeddingChartMap : (mixedEmbeddingDomain e o o' U V ι).toScheme ⟶
    (M).toScheme := (g) ∣_ M

instance mixedEmbeddingChartMap_open : IsOpenImmersion
    (mixedEmbeddingChartMap e o o' U V ι) := by
  let _ := subframeGraph_isOpenImmersion e o o' ι
  exact inferInstanceAs (IsOpenImmersion ((g) ∣_ M))

omit [Etale p] in
/-- The restricted graph retains its actual original mixed morphism. -/
@[reassoc] theorem mixedEmbeddingChartMap_inclusion :
    mixedEmbeddingChartMap e o o' U V ι ≫ (M).ι =
      (mixedEmbeddingDomain e o o' U V ι).ι ≫ (g) :=
  morphismRestrict_ι (g) M

/-- The image is exactly the retained embedding piece, not a larger source neighborhood. -/
theorem mixedEmbeddingChartMap_range :
    (mixedEmbeddingChartMap e o o' U V ι).opensRange =
      mixedEmbeddingTestOpen e o o' (M).ι ι := by
  ext x
  change (∃ y, mixedEmbeddingChartMap e o o' U V ι y = x) ↔
    ∃ y, (g) y = (M).ι x
  constructor
  · rintro ⟨y, rfl⟩
    exact ⟨y.val, (congrArg (fun f ↦ f y)
      (mixedEmbeddingChartMap_inclusion e o o' U V ι)).symm⟩
  · rintro ⟨y, hy⟩
    have hm : y ∈ mixedEmbeddingDomain e o o' U V ι := by
      change (g) y ∈ M
      rw [hy]
      exact x.property
    refine ⟨⟨y, hm⟩, ?_⟩
    apply Subtype.ext
    exact (congrArg (fun f ↦ f ⟨y, hm⟩)
      (mixedEmbeddingChartMap_inclusion e o o' U V ι)).trans hy

/-- The whole embedding branch is an actual source open with its nilpotent structure. -/
def mixedEmbeddingDomainIso : (mixedEmbeddingDomain e o o' U V ι).toScheme ≅
    (mixedEmbeddingTestOpen e o o' (M).ι ι).toScheme :=
  (mixedEmbeddingChartMap e o o' U V ι).isoOpensRange ≪≫
    Scheme.isoOfEq _ (mixedEmbeddingChartMap_range e o o' U V ι)

/-- The source-open identification retains the actual full mixed-relation morphism. -/
@[reassoc] theorem mixedEmbeddingDomainIso_inclusion :
    (mixedEmbeddingDomainIso e o o' U V ι).hom ≫
      (mixedEmbeddingTestOpen e o o' (M).ι ι).ι =
        mixedEmbeddingChartMap e o o' U V ι := by
  simp only [mixedEmbeddingDomainIso, Iso.trans_hom, Category.assoc,
    Scheme.isoOfEq_hom_ι, Scheme.Hom.isoOpensRange_hom_ι]

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
