/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowChartImageClosure
public import FLT.Mazur.ChowProjectiveProduct

/-!
# The image of the common Chow open in the projective product

Take the scheme-theoretic image of the constructed common-open tuple. Its
coordinate maps factor through the chart images by containment of their
kernel ideals. These factorizations are proper over each chart image and
retain both the common-open components and the original field structure.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow.ChartData

variable {k : Type u} [Field k] {X : Scheme.{u}} {f : X ⟶ Spec (.of k)}
  (D : ChartData f) [LocallyOfFiniteType f] [QuasiCompact f]

instance commonToProduct_quasiCompact : QuasiCompact D.commonToProduct := by
  let _noetherian := source_isNoetherian f
  have : NoetherianSpace D.common.toScheme := NoetherianSpace.set (D.common : Set X)
  exact quasiCompact_of_noetherianSpace_source _

/-- The actual scheme-theoretic image of the common-open tuple. -/
def productImage : Scheme.{u} := D.commonToProduct.image

/-- The canonical closed embedding in the finite projective product. -/
def productImageι : D.productImage ⟶ D.projectiveProduct := D.commonToProduct.imageι

instance productImageι_isClosedImmersion : IsClosedImmersion D.productImageι := by
  dsimp [productImageι]
  infer_instance

/-- The common open factors canonically through its product image. -/
def commonToProductImage : D.common.toScheme ⟶ D.productImage := D.commonToProduct.toImage

omit [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma commonToProductImage_ι :
    D.commonToProductImage ≫ D.productImageι = D.commonToProduct :=
  D.commonToProduct.toImage_imageι

instance commonToProductImage_schemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant D.commonToProductImage :=
  toImage_schemeTheoreticallyDominant _

/-- The structure morphism inherited from the finite projective product. -/
def productImageProjection : D.productImage ⟶ Spec (.of k) :=
  D.productImageι ≫ D.projectiveProductProjection

instance productImageProjection_isProper : IsProper D.productImageProjection := by
  dsimp [productImageProjection]
  infer_instance

omit [LocallyOfFiniteType f] [QuasiCompact f] in
@[reassoc (attr := simp)]
lemma commonToProductImage_projection :
    D.commonToProductImage ≫ D.productImageProjection = D.common.ι ≫ f := by
  simp [productImageProjection, ← Category.assoc]

/-- The kernel of each product-image coordinate is exactly the chart image
ideal, because the common open is schematically dense in both images. -/
lemma productImage_coordinate_ker (i : D.Index) :
    (D.productImageι ≫ D.projectiveProductπ i).ker = (D.chartImageι i).ker := by
  calc
    (D.productImageι ≫ D.projectiveProductπ i).ker =
        (D.commonToProductImage ≫ (D.productImageι ≫ D.projectiveProductπ i)).ker := by
      rw [Scheme.Hom.ker_comp D.commonToProductImage,
        D.commonToProductImage.ker_eq_bot, Scheme.IdealSheafData.map_bot]
    _ = (D.commonToProjective i).ker := by simp [← Category.assoc]
    _ = (D.chartImageι i).ker := (D.chartImageι_ker i).symm

/-- Kernel containment constructs the coordinate factorization through the
closed chart image, without an additional geometric choice. -/
def productImageToChartImage (i : D.Index) : D.productImage ⟶ D.chartImage i :=
  IsClosedImmersion.lift (D.chartImageι i) (D.productImageι ≫ D.projectiveProductπ i)
    (D.productImage_coordinate_ker i).ge

@[reassoc (attr := simp)]
lemma productImageToChartImage_ι (i : D.Index) :
    D.productImageToChartImage i ≫ D.chartImageι i =
      D.productImageι ≫ D.projectiveProductπ i :=
  IsClosedImmersion.lift_fac _ _ _

/-- The factorization agrees with the original common-open chart component. -/
@[reassoc (attr := simp)]
lemma commonToProductImage_toChartImage (i : D.Index) :
    D.commonToProductImage ≫ D.productImageToChartImage i = D.commonToChartImage i := by
  rw [← cancel_mono (D.chartImageι i)]
  rw [Category.assoc, D.productImageToChartImage_ι, ← Category.assoc,
    D.commonToProductImage_ι, D.commonToProduct_π, D.commonToChartImage_ι]

/-- Each factored coordinate remains a morphism over the field. -/
@[reassoc (attr := simp)]
lemma productImageToChartImage_projection (i : D.Index) :
    D.productImageToChartImage i ≫ D.chartImageProjection i =
      D.productImageProjection := by
  rw [chartImageProjection, ← Category.assoc, D.productImageToChartImage_ι,
    Category.assoc, D.projectiveProductπ_baseProjection]
  rfl

/-- Properness over the field and separatedness of the chart image imply
properness of the constructed projection to that image. -/
instance productImageToChartImage_isProper (i : D.Index) :
    IsProper (D.productImageToChartImage i) := by
  have : IsProper (D.productImageToChartImage i ≫ D.chartImageProjection i) := by
    rw [D.productImageToChartImage_projection]
    infer_instance
  exact IsProper.of_comp _ (D.chartImageProjection i)

/-- The common-open factorization also proves schematic dominance of every
projection to a chart image. -/
instance productImageToChartImage_schemeTheoreticallyDominant (i : D.Index) :
    IsSchemeTheoreticallyDominant (D.productImageToChartImage i) := by
  constructor
  apply le_bot_iff.mp
  calc
    (D.productImageToChartImage i).ker ≤
        (D.commonToProductImage ≫ D.productImageToChartImage i).ker :=
      D.commonToProductImage.le_ker_comp _
    _ = ⊥ := by rw [D.commonToProductImage_toChartImage, Scheme.Hom.ker_eq_bot]

/-- Since these projections are proper and schematically dominant, they are
surjective on points of the actual chart images. -/
lemma productImageToChartImage_surjective (i : D.Index) :
    Function.Surjective (D.productImageToChartImage i) := by
  rw [← Set.range_eq_univ,
    ← (D.productImageToChartImage i).isClosedMap.isClosed_range.closure_eq]
  exact (D.productImageToChartImage i).denseRange.closure_eq

end FLT.Mazur.Chow.ChartData
