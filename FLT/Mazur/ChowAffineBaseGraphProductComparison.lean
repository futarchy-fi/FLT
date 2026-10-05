/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowAffineBaseGraphClosure
public import FLT.Mazur.ChowAffineBaseProductOpenProper

/-!
# Affine-base Comparing the Chow graph with the open product image

The inverse image of each source chart under the glued map is exactly its
product chart open. This proves properness locally on the source closure.
The closed graphs then identify the union with the existing graph closure.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.Chow.AffineBase

variable {R : CommRingCat.{u}} [IsNoetherianRing R] {X : Scheme.{u}} (f : X ⟶ Spec R)
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

end FLT.Mazur.Chow.AffineBase
