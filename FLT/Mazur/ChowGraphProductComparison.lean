/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowGraphEmbedding
public import FLT.Mazur.ChowProductOpenGluing

/-!
# Comparing the Chow graph with the open product image

The inverse image of each source chart under the glued map is exactly its
product chart open. This proves properness locally on the source closure.
The closed graphs then identify the union with the existing graph closure.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.Chow.ChartData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (D : ChartData f) [LocallyOfFiniteType f] [QuasiCompact f]

omit [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma sourceChartToImage_projection (i : D.Index) :
    D.sourceChartToImage i ≫ D.chartImageProjection i =
      (D.sourceChart i).ι ≫ D.sourceClosureι ≫ f := by
  rw [chartImageProjection, ← Category.assoc, sourceChartToImage_ι,
    sourceChartToProjective, Category.assoc, D.over_base,
    ← Category.assoc, sourceChartToChart, morphismRestrict_ι]
  rfl

/-- The local projection is the base change of the proper chart-image projection. -/
lemma productChartToSourceChart_isPullback (i : D.Index) :
    IsPullback (D.productChartToSourceChart i) (D.productChartOpen i).ι
      (D.sourceChartToImage i) (D.productImageToChartImage i) :=
  IsOpenImmersion.isPullback _ _ _ _ (D.productChartToSourceChart_image i).symm
    (by rw [Scheme.Opens.opensRange_ι]; rfl)

instance productChartToSourceChart_isProper (i : D.Index) :
    IsProper (D.productChartToSourceChart i) :=
  MorphismProperty.of_isPullback (D.productChartToSourceChart_isPullback i).flip inferInstance

/-- If a local source map lands in another source chart, its product point
already belongs to the corresponding product open. -/
lemma productChartToSource_preimage_le (i j : D.Index) :
    D.productChartToSource i ⁻¹ᵁ D.sourceChart j ≤
      (D.productChartOpen i).ι ⁻¹ᵁ D.productChartOpen j := by
  let V := D.productChartToSource i ⁻¹ᵁ D.sourceChart j
  let a : V.toScheme ⟶ D.chartImage j :=
    V.ι ≫ (D.productChartOpen i).ι ≫ D.productImageToChartImage j
  let b : V.toScheme ⟶ D.chartImage j :=
    (D.productChartToSource i ∣_ D.sourceChart j) ≫ D.sourceChartToImage j
  have hr : Set.range (D.commonToProductChart i) ⊆ Set.range V.ι := by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨x, rfl⟩
    change D.productChartToSource i (D.commonToProductChart i x) ∈ D.sourceChart j
    rw [← Scheme.Hom.comp_apply, D.commonToProductChart_source]
    rw [← D.commonToSourceChart_ι j, Scheme.Hom.comp_apply]
    exact (D.commonToSourceChart j x).property
  let t := IsOpenImmersion.lift V.ι (D.commonToProductChart i) hr
  have ht : t ≫ (V.ι ≫ (D.productChartOpen i).ι) = D.commonToProductImage := by
    simp [t, ← Category.assoc]
  have : QuasiCompact (t ≫ (V.ι ≫ (D.productChartOpen i).ι)) := by
    rw [ht]
    let _noetherian := source_isNoetherian f
    have : NoetherianSpace D.common.toScheme := NoetherianSpace.set (D.common : Set X)
    exact quasiCompact_of_noetherianSpace_source _
  have : IsSchemeTheoreticallyDominant (t ≫ (V.ι ≫ (D.productChartOpen i).ι)) := by
    rw [ht]
    infer_instance
  have : IsSchemeTheoreticallyDominant t :=
    schematicallyDense_openFactor t (V.ι ≫ (D.productChartOpen i).ι)
  have hab : a = b := by
    refine schematicallyDense_ext (D.chartImageProjection j) ?_ t ?_
    · simp only [a, b, Category.assoc, productImageToChartImage_projection,
        sourceChartToImage_projection]
      rw [morphismRestrict_ι_assoc, productChartToSource_projection]
    · have hc : t ≫ (D.productChartToSource i ∣_ D.sourceChart j) =
          D.commonToSourceChart j := by
        rw [← cancel_mono (D.sourceChart j).ι]
        rw [Category.assoc, morphismRestrict_ι, ← Category.assoc]
        change (t ≫ V.ι) ≫ D.productChartToSource i = _
        rw [IsOpenImmersion.lift_fac, commonToProductChart_source,
          commonToSourceChart_ι]
      dsimp only [a, b]
      rw [← Category.assoc V.ι (D.productChartOpen i).ι,
        ← Category.assoc t (V.ι ≫ (D.productChartOpen i).ι), ht,
        commonToProductImage_toChartImage, ← Category.assoc, hc]
      rfl
  intro x hx
  have habx := congrArg (fun e : V.toScheme ⟶ D.chartImage j ↦ e ⟨x, hx⟩) hab
  change D.productImageToChartImage j ((D.productChartOpen i).ι x) ∈
    Set.range (D.sourceChartToImage j)
  exact ⟨(D.productChartToSource i ∣_ D.sourceChart j) ⟨x, hx⟩, habx.symm⟩

/-- The glued map has exactly the prescribed product opens over the source charts. -/
lemma productOpenToSource_preimage [IsSeparated f] (j : D.Index) :
    D.productOpenToSource ⁻¹ᵁ D.sourceChart j = (D.productOpenCover.f j).opensRange := by
  ext x
  constructor
  · intro hx
    obtain ⟨i, y, rfl⟩ := D.productOpenCover.exists_eq x
    have hy : D.productChartToSource i y ∈ D.sourceChart j := by
      change D.productOpenToSource (D.productOpenCover.f i y) ∈ D.sourceChart j at hx
      rw [← Scheme.Hom.comp_apply, productOpenCover_toSource] at hx
      exact hx
    have hz := D.productChartToSource_preimage_le i j hy
    refine ⟨⟨y.val, hz⟩, ?_⟩
    apply D.productOpenUnion.ι.isEmbedding.injective
    change (D.productOpenCover.f j ≫ D.productOpenUnion.ι) _ =
      (D.productOpenCover.f i ≫ D.productOpenUnion.ι) _
    rw [productOpenCover_ι, productOpenCover_ι]
    rfl
  · rintro ⟨y, rfl⟩
    change D.productOpenToSource (D.productOpenCover.f j y) ∈ D.sourceChart j
    rw [← Scheme.Hom.comp_apply, productOpenCover_toSource]
    exact (D.productChartToSourceChart j y).property

/-- The product opens are the actual pullbacks of the source chart cover. -/
lemma productOpenToSource_isPullback [IsSeparated f] (i : D.Index) :
    IsPullback (D.productChartToSourceChart i) (D.productOpenCover.f i)
      (D.sourceChart i).ι D.productOpenToSource :=
  IsOpenImmersion.isPullback _ _ _ _ (D.productOpenCover_toSource i)
    (by rw [Scheme.Opens.opensRange_ι]; exact D.productOpenToSource_preimage i)

/-- Properness follows from the proper local projections on the source chart cover. -/
instance productOpenToSource_isProper [IsSeparated f] : IsProper D.productOpenToSource := by
  apply IsZariskiLocalAtTarget.of_iSup_eq_top D.sourceChart D.sourceClosure_covers
  intro i
  have H := D.productOpenToSource_isPullback i
  have : IsProper (pullback.snd D.productOpenToSource (D.sourceChart i).ι) := by
    have H' := H.flip
    rw [← H'.isoPullback_inv_snd]
    infer_instance
  dsimp [morphismRestrict]
  infer_instance

/-- The common open lands in the union, also for empty source schemes. -/
lemma commonToProductImage_range_union :
    Set.range D.commonToProductImage ⊆ Set.range D.productOpenUnion.ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  have hx : D.common.ι x ∈ ⨆ i, D.opens i := by rw [D.covers]; trivial
  obtain ⟨i, _⟩ := Opens.mem_iSup.mp hx
  apply (le_iSup D.productChartOpen i)
  rw [← D.commonToProductChart_ι i, Scheme.Hom.comp_apply]
  exact (D.commonToProductChart i x).property

/-- The original common open factored through the constructed union. -/
def commonToProductOpen : D.common.toScheme ⟶ D.productOpenUnion.toScheme :=
  IsOpenImmersion.lift D.productOpenUnion.ι D.commonToProductImage
    D.commonToProductImage_range_union

@[reassoc (attr := simp)]
lemma commonToProductOpen_ι :
    D.commonToProductOpen ≫ D.productOpenUnion.ι = D.commonToProductImage :=
  IsOpenImmersion.lift_fac _ _ _

lemma commonToProductOpen_eq (i : D.Index) :
    D.commonToProductOpen = D.commonToProductChart i ≫ D.productOpenCover.f i := by
  rw [← cancel_mono D.productOpenUnion.ι]
  simp only [commonToProductOpen_ι, Category.assoc,
    productOpenCover_ι, commonToProductChart_ι]

@[reassoc (attr := simp)]
lemma commonToProductOpen_source [IsSeparated f] :
    D.commonToProductOpen ≫ D.productOpenToSource = D.commonToSourceClosure := by
  classical
  by_cases hi : Nonempty D.Index
  · rw [D.commonToProductOpen_eq (Classical.choice hi)]
    simp only [Category.assoc, productOpenCover_toSource, commonToProductChart_source]
  · have : IsEmpty D.common.toScheme := ⟨fun x ↦ by
      have hx : D.common.ι x ∈ ⨆ i, D.opens i := by rw [D.covers]; trivial
      obtain ⟨i, _⟩ := Opens.mem_iSup.mp hx
      exact hi ⟨i⟩⟩
    exact isInitialOfIsEmpty.hom_ext _ _

instance commonToProductOpen_schemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant D.commonToProductOpen := by
  have : QuasiCompact (D.commonToProductOpen ≫ D.productOpenUnion.ι) := by
    rw [D.commonToProductOpen_ι]
    let _noetherian := source_isNoetherian f
    have : NoetherianSpace D.common.toScheme := NoetherianSpace.set (D.common : Set X)
    exact quasiCompact_of_noetherianSpace_source _
  have : IsSchemeTheoreticallyDominant (D.commonToProductOpen ≫ D.productOpenUnion.ι) := by
    rw [D.commonToProductOpen_ι]
    infer_instance
  exact schematicallyDense_openFactor D.commonToProductOpen D.productOpenUnion.ι

end FLT.Mazur.Chow.ChartData

namespace FLT.Mazur.Chow

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The graph of the glued map, in the same ambient product as the graph closure. -/
def productOpenGraph : (chartData f).productOpenUnion.toScheme ⟶ graphAmbient f :=
  pullback.lift (chartData f).productOpenToSource
    ((chartData f).productOpenUnion.ι ≫ (chartData f).productImageι)
    (by simpa only [Category.assoc, graphSourceProjection, ChartData.productImageProjection]
      using (chartData f).productOpenToSource_projection)

@[reassoc (attr := simp)]
lemma productOpenGraph_fst :
    productOpenGraph f ≫ graphAmbientFst f = (chartData f).productOpenToSource :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma productOpenGraph_snd :
    productOpenGraph f ≫ graphAmbientSnd f =
      (chartData f).productOpenUnion.ι ≫ (chartData f).productImageι :=
  pullback.lift_snd _ _ _

instance productOpenGraph_isImmersion : IsImmersion (productOpenGraph f) := by
  have : IsImmersion (productOpenGraph f ≫ graphAmbientSnd f) := by
    rw [productOpenGraph_snd]
    infer_instance
  exact IsImmersion.of_comp _ (graphAmbientSnd f)

instance productOpenGraph_isProper : IsProper (productOpenGraph f) := by
  have : IsProper (productOpenGraph f ≫ graphAmbientFst f) := by
    rw [productOpenGraph_fst]
    infer_instance
  exact IsProper.of_comp _ (graphAmbientFst f)

/-- Properness makes the immersed graph closed in the original ambient product. -/
instance productOpenGraph_isClosedImmersion : IsClosedImmersion (productOpenGraph f) :=
  IsClosedImmersion.of_isPreimmersion _ (productOpenGraph f).isClosedMap.isClosed_range

@[reassoc (attr := simp)]
lemma commonToProductOpen_graph :
    (chartData f).commonToProductOpen ≫ productOpenGraph f = commonToGraphAmbient f := by
  apply pullback.hom_ext
  · change _ ≫ graphAmbientFst f = commonToGraphAmbient f ≫ graphAmbientFst f
    simp only [Category.assoc, productOpenGraph_fst,
      ChartData.commonToProductOpen_source, commonToGraphAmbient_fst]
  · change _ ≫ graphAmbientSnd f = commonToGraphAmbient f ≫ graphAmbientSnd f
    simp only [Category.assoc, productOpenGraph_snd,
      ChartData.commonToProductOpen_ι_assoc, ChartData.commonToProductImage_ι,
      commonToGraphAmbient_snd]

/-- Both closed graphs have exactly the ideal of the original common-open graph. -/
lemma productOpenGraph_ker : (productOpenGraph f).ker = (graphClosureι f).ker := by
  calc
    (productOpenGraph f).ker =
        ((chartData f).commonToProductOpen ≫ productOpenGraph f).ker := by
      rw [Scheme.Hom.ker_comp, (chartData f).commonToProductOpen.ker_eq_bot,
        Scheme.IdealSheafData.map_bot]
    _ = (commonToGraphAmbient f).ker := by rw [commonToProductOpen_graph]
    _ = (graphClosureι f).ker := by
      rw [← commonToGraphClosure_ι, Scheme.Hom.ker_comp,
        (commonToGraphClosure f).ker_eq_bot, Scheme.IdealSheafData.map_bot]

/-- The comparison is constructed from the equality of the two closed graph ideals. -/
def graphClosureToProductOpen : graphClosure f ⟶ (chartData f).productOpenUnion.toScheme :=
  IsClosedImmersion.lift (productOpenGraph f) (graphClosureι f) (productOpenGraph_ker f).le

@[reassoc (attr := simp)]
lemma graphClosureToProductOpen_graph :
    graphClosureToProductOpen f ≫ productOpenGraph f = graphClosureι f :=
  IsClosedImmersion.lift_fac _ _ _

instance graphClosureToProductOpen_isIso : IsIso (graphClosureToProductOpen f) :=
  IsClosedImmersion.isIso_lift _ _ (productOpenGraph_ker f)

/-- The existing graph closure is canonically the constructed open in the product image. -/
def graphClosureProductOpenIso : graphClosure f ≅ (chartData f).productOpenUnion.toScheme :=
  asIso (graphClosureToProductOpen f)

/-- The comparison retains the original map to the finite projective product. -/
@[reassoc]
lemma graphClosureToProductOpen_product :
    graphClosureToProductOpen f ≫ (chartData f).productOpenUnion.ι ≫
      (chartData f).productImageι = graphClosureToProduct f := by
  rw [← productOpenGraph_snd, ← Category.assoc, graphClosureToProductOpen_graph]
  rfl

/-- The comparison also retains the original modification map to the source. -/
@[reassoc]
lemma graphClosureToProductOpen_source :
    graphClosureToProductOpen f ≫ (chartData f).productOpenToSource ≫
      (chartData f).sourceClosureι = graphClosureπ f := by
  rw [← productOpenGraph_fst, ← Category.assoc,
    ← Category.assoc, graphClosureToProductOpen_graph]
  rfl

/-- The graph closure's original product map is an immersion. -/
instance graphClosureToProduct_isImmersion : IsImmersion (graphClosureToProduct f) := by
  rw [← graphClosureToProductOpen_product]
  infer_instance

end FLT.Mazur.Chow
