/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowProductImageFactors

/-!
# Gluing the open charts of the Chow product image

The inverse images of the source charts in their projective closures carry
maps to the source closure. Schematic density and separatedness identify
these maps on overlaps, so they glue on the union of these actual opens.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow

/-- Schematic density detects equality of morphisms to a separated target,
including when the source has nilpotents. -/
lemma schematicallyDense_ext {A B T S : Scheme.{u}} {a b : A ⟶ B}
    (s : B ⟶ S) [IsSeparated s] (h : a ≫ s = b ≫ s)
    (t : T ⟶ A) [IsSchemeTheoreticallyDominant t] (ht : t ≫ a = t ≫ b) : a = b := by
  let A' : Over S := Over.mk (a ≫ s)
  let B' : Over S := Over.mk s
  let T' : Over S := Over.mk (t ≫ a ≫ s)
  let a' : A' ⟶ B' := Over.homMk a
  let b' : A' ⟶ B' := Over.homMk b h.symm
  let t' : T' ⟶ A' := Over.homMk t
  have : IsSeparated B'.hom := ‹_›
  have ht' : t' ≫ a' = t' ≫ b' := by ext1; exact ht
  have he : (equalizer.lift t' ht').left ≫ (equalizer.ι a' b').left = t :=
    congrArg Over.Hom.left (equalizer.lift_ι t' ht')
  have : IsIso (equalizer.ι a' b').left := by
    apply IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
    apply le_bot_iff.mp
    calc
      _ ≤ ((equalizer.lift t' ht').left ≫ (equalizer.ι a' b').left).ker :=
        Scheme.Hom.le_ker_comp _ _
      _ = ⊥ := by rw [he, t.ker_eq_bot]
  rw [← cancel_epi (equalizer.ι a' b').left]
  exact congrArg Over.Hom.left (equalizer.condition a' b')

/-- A schematically dense map remains dense after factoring through an open. -/
lemma schematicallyDense_openFactor {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    [IsOpenImmersion b] [QuasiCompact (a ≫ b)]
    [IsSchemeTheoreticallyDominant (a ≫ b)] : IsSchemeTheoreticallyDominant a := by
  have hr : Set.range (a ≫ b) ⊆ Set.range b := by
    rintro _ ⟨x, rfl⟩
    exact ⟨a x, rfl⟩
  have he : a = IsOpenImmersion.lift b (a ≫ b) hr := by
    rw [← cancel_mono b, IsOpenImmersion.lift_fac]
  rw [he]
  exact IsSchemeTheoreticallyDominant.of_isPullback
    (IsOpenImmersion.isPullback_lift_id (a ≫ b) b hr).flip

namespace ChartData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (D : ChartData f) [LocallyOfFiniteType f] [QuasiCompact f]

/-- The inverse image of the source chart open inside its projective image. -/
def productChartOpen (i : D.Index) : D.productImage.Opens :=
  D.productImageToChartImage i ⁻¹ᵁ (D.sourceChartToImage i).opensRange

/-- The map from the product open to the corresponding source chart. -/
def productChartToSourceChart (i : D.Index) :
    (D.productChartOpen i).toScheme ⟶ (D.sourceChart i).toScheme :=
  IsOpenImmersion.lift (D.sourceChartToImage i)
    ((D.productChartOpen i).ι ≫ D.productImageToChartImage i) (by
      rintro _ ⟨x, rfl⟩
      exact x.property)

@[reassoc (attr := simp)]
lemma productChartToSourceChart_image (i : D.Index) :
    D.productChartToSourceChart i ≫ D.sourceChartToImage i =
      (D.productChartOpen i).ι ≫ D.productImageToChartImage i :=
  IsOpenImmersion.lift_fac _ _ _

/-- Each local map is a map to the actual scheme-theoretic source closure. -/
def productChartToSource (i : D.Index) :
    (D.productChartOpen i).toScheme ⟶ D.sourceClosure :=
  D.productChartToSourceChart i ≫ (D.sourceChart i).ι

/-- The common open lies in every product chart open. -/
lemma commonToProductImage_range_productChart (i : D.Index) :
    Set.range D.commonToProductImage ⊆ Set.range (D.productChartOpen i).ι := by
  rw [Scheme.Opens.range_ι]
  rintro _ ⟨x, rfl⟩
  change D.productImageToChartImage i (D.commonToProductImage x) ∈
    Set.range (D.sourceChartToImage i)
  rw [← Scheme.Hom.comp_apply, D.commonToProductImage_toChartImage]
  exact ⟨D.commonToSourceChart i x, rfl⟩

/-- The canonical common-open map into each product chart open. -/
def commonToProductChart (i : D.Index) :
    D.common.toScheme ⟶ (D.productChartOpen i).toScheme :=
  IsOpenImmersion.lift (D.productChartOpen i).ι D.commonToProductImage
    (D.commonToProductImage_range_productChart i)

@[reassoc (attr := simp)]
lemma commonToProductChart_ι (i : D.Index) :
    D.commonToProductChart i ≫ (D.productChartOpen i).ι = D.commonToProductImage :=
  IsOpenImmersion.lift_fac _ _ _

@[reassoc (attr := simp)]
lemma commonToProductChart_sourceChart (i : D.Index) :
    D.commonToProductChart i ≫ D.productChartToSourceChart i =
      D.commonToSourceChart i := by
  rw [← cancel_mono (D.sourceChartToImage i)]
  simp only [Category.assoc, productChartToSourceChart_image,
    commonToProductChart_ι_assoc, commonToProductImage_toChartImage]
  rfl

@[reassoc (attr := simp)]
lemma commonToProductChart_source (i : D.Index) :
    D.commonToProductChart i ≫ D.productChartToSource i = D.commonToSourceClosure := by
  simp [productChartToSource, ← Category.assoc]

/-- Each local map respects the structure morphism to the field. -/
@[reassoc (attr := simp)]
lemma productChartToSource_projection (i : D.Index) :
    D.productChartToSource i ≫ (D.sourceClosureι ≫ f) =
      (D.productChartOpen i).ι ≫ D.productImageProjection := by
  have hi : D.sourceChartToImage i ≫ D.chartImageProjection i =
      (D.sourceChart i).ι ≫ D.sourceClosureι ≫ f := by
    rw [chartImageProjection, ← Category.assoc, sourceChartToImage_ι,
      sourceChartToProjective, Category.assoc, D.over_base,
      ← Category.assoc, sourceChartToChart, morphismRestrict_ι]
    rfl
  rw [productChartToSource, Category.assoc, ← hi, ← Category.assoc,
    productChartToSourceChart_image, Category.assoc, productImageToChartImage_projection]

/-- The union on which the local maps will glue. -/
def productOpenUnion : D.productImage.Opens := ⨆ i, D.productChartOpen i

/-- The canonical cover of the union by the product chart opens. -/
abbrev productOpenCover : D.productOpenUnion.toScheme.OpenCover :=
  Scheme.Opens.iSupOpenCover D.productChartOpen

@[reassoc (attr := simp)]
lemma productOpenCover_ι (i : D.Index) :
    D.productOpenCover.f i ≫ D.productOpenUnion.ι = (D.productChartOpen i).ι :=
  Scheme.homOfLE_ι _ (le_iSup _ i)

/-- The two local source maps agree on every overlap of the canonical cover. -/
lemma productChartToSource_overlap [IsSeparated f] (i j : D.Index) :
    pullback.fst (D.productOpenCover.f i) (D.productOpenCover.f j) ≫
      D.productChartToSource i =
    pullback.snd (D.productOpenCover.f i) (D.productOpenCover.f j) ≫
      D.productChartToSource j := by
  let p := pullback.fst (D.productOpenCover.f i) (D.productOpenCover.f j)
  let q := pullback.snd (D.productOpenCover.f i) (D.productOpenCover.f j)
  have hpq : p ≫ (D.productChartOpen i).ι = q ≫ (D.productChartOpen j).ι := by
    simpa only [Category.assoc, productOpenCover_ι] using
      congrArg (fun e ↦ e ≫ D.productOpenUnion.ι)
        (pullback.condition (f := D.productOpenCover.f i) (g := D.productOpenCover.f j))
  let t : D.common.toScheme ⟶
      pullback (D.productOpenCover.f i) (D.productOpenCover.f j) :=
    pullback.lift (D.commonToProductChart i) (D.commonToProductChart j) (by
    rw [← cancel_mono D.productOpenUnion.ι]
    simp only [Category.assoc, productOpenCover_ι, commonToProductChart_ι])
  have ht : t ≫ (p ≫ (D.productChartOpen i).ι) = D.commonToProductImage := by
    simp [t, p, ← Category.assoc]
  have : QuasiCompact (t ≫ (p ≫ (D.productChartOpen i).ι)) := by
    rw [ht]
    let _noetherian := source_isNoetherian f
    have : NoetherianSpace D.common.toScheme := NoetherianSpace.set (D.common : Set X)
    exact quasiCompact_of_noetherianSpace_source _
  have : IsSchemeTheoreticallyDominant (t ≫ (p ≫ (D.productChartOpen i).ι)) := by
    rw [ht]
    infer_instance
  have : IsSchemeTheoreticallyDominant t :=
    schematicallyDense_openFactor t (p ≫ (D.productChartOpen i).ι)
  refine schematicallyDense_ext (D.sourceClosureι ≫ f) ?_ t ?_
  · simp only [Category.assoc, productChartToSource_projection]
    exact congrArg (fun e ↦ e ≫ D.productImageProjection) hpq
  · simp [t, ← Category.assoc]

/-- The map obtained by gluing the actual local maps on their union. -/
def productOpenToSource [IsSeparated f] :
    D.productOpenUnion.toScheme ⟶ D.sourceClosure :=
  D.productOpenCover.glueMorphisms D.productChartToSource D.productChartToSource_overlap

@[reassoc (attr := simp)]
lemma productOpenCover_toSource [IsSeparated f] (i : D.Index) :
    D.productOpenCover.f i ≫ D.productOpenToSource = D.productChartToSource i :=
  D.productOpenCover.ι_glueMorphisms _ _ i

/-- The glued map retains the structure morphism of the product image. -/
@[reassoc (attr := simp)]
lemma productOpenToSource_projection [IsSeparated f] :
    D.productOpenToSource ≫ (D.sourceClosureι ≫ f) =
      D.productOpenUnion.ι ≫ D.productImageProjection := by
  apply D.productOpenCover.hom_ext
  intro i
  rw [← Category.assoc, productOpenCover_toSource,
    productChartToSource_projection, ← Category.assoc, productOpenCover_ι]

end ChartData

end FLT.Mazur.Chow
