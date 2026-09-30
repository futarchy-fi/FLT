/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowGraphClosure

/-!
# The Chow graph embedding over the original source

The graph closure was constructed over the scheme-theoretic source closure.
Base changing its closed inclusion into the original source embeds that
ambient product into the product over the original source. Composing gives
a closed embedding whose two projections are the modification and its
projective-product map. This supplies the relative product embedding before
the Segre construction.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The finite projective product base changed to the original source. -/
def graphSourceProduct : Scheme.{u} :=
  pullback f (chartData f).projectiveProductProjection

/-- The projection to the original source. -/
def graphSourceProductFst : graphSourceProduct f ⟶ X := pullback.fst _ _

/-- The projection to the original finite projective product. -/
def graphSourceProductSnd : graphSourceProduct f ⟶ (chartData f).projectiveProduct :=
  pullback.snd _ _

@[reassoc]
lemma graphSourceProduct_condition :
    graphSourceProductFst f ≫ f =
      graphSourceProductSnd f ≫ (chartData f).projectiveProductProjection := pullback.condition

/-- The original graph ambient scheme embeds by its two existing coordinates. -/
def graphAmbientInclusion : graphAmbient f ⟶ graphSourceProduct f :=
  pullback.lift (graphAmbientFst f ≫ (chartData f).sourceClosureι)
    (graphAmbientSnd f) (by
      simpa only [Category.assoc, graphSourceProjection] using graphAmbient_condition f)

@[reassoc (attr := simp)]
lemma graphAmbientInclusion_fst :
    graphAmbientInclusion f ≫ graphSourceProductFst f =
      graphAmbientFst f ≫ (chartData f).sourceClosureι := pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma graphAmbientInclusion_snd :
    graphAmbientInclusion f ≫ graphSourceProductSnd f = graphAmbientSnd f :=
  pullback.lift_snd _ _ _

/-- The ambient inclusion is the base change of the closed source inclusion. -/
lemma graphAmbientInclusion_isPullback :
    IsPullback (graphAmbientInclusion f) (graphAmbientFst f)
      (graphSourceProductFst f) (chartData f).sourceClosureι := by
  apply IsPullback.of_right (h₁₂ := graphSourceProductSnd f)
    (h₂₂ := f) (v₁₃ := (chartData f).projectiveProductProjection)
    ?_ (graphAmbientInclusion_fst f)
    (IsPullback.of_hasPullback f (chartData f).projectiveProductProjection).flip
  rw [graphAmbientInclusion_snd]
  exact (IsPullback.of_hasPullback (graphSourceProjection f)
    (chartData f).projectiveProductProjection).flip

/-- Closed immersions remain closed under the displayed base change. -/
instance graphAmbientInclusion_isClosedImmersion :
    IsClosedImmersion (graphAmbientInclusion f) :=
  MorphismProperty.of_isPullback (graphAmbientInclusion_isPullback f).flip inferInstance

/-- The actual closed embedding of the graph closure over the original source. -/
def graphClosureEmbedding : graphClosure f ⟶ graphSourceProduct f :=
  graphClosureι f ≫ graphAmbientInclusion f

instance graphClosureEmbedding_isClosedImmersion :
    IsClosedImmersion (graphClosureEmbedding f) := by
  dsimp [graphClosureEmbedding]
  infer_instance

/-- The first coordinate is the proper surjective modification already constructed. -/
@[reassoc (attr := simp)]
lemma graphClosureEmbedding_fst :
    graphClosureEmbedding f ≫ graphSourceProductFst f = graphClosureπ f := by
  simp [graphClosureEmbedding, graphClosureπ, Category.assoc]

/-- The second coordinate is the retained map to the finite projective product. -/
@[reassoc (attr := simp)]
lemma graphClosureEmbedding_snd :
    graphClosureEmbedding f ≫ graphSourceProductSnd f = graphClosureToProduct f := by
  simp [graphClosureEmbedding, graphClosureToProduct, Category.assoc]

/-- The embedding is exactly the pair of the modification and product maps. -/
lemma graphClosureEmbedding_eq_lift :
    graphClosureEmbedding f = pullback.lift (graphClosureπ f) (graphClosureToProduct f)
      (graphClosureToProduct_projection f).symm := by
  apply pullback.hom_ext
  · exact (graphClosureEmbedding_fst f).trans (pullback.lift_fst _ _ _).symm
  · exact (graphClosureEmbedding_snd f).trans (pullback.lift_snd _ _ _).symm

/-- On the common open the embedding retains the original source and chart tuple. -/
lemma commonToGraphClosure_embedding :
    commonToGraphClosure f ≫ graphClosureEmbedding f =
      pullback.lift (chartData f).common.ι (chartData f).commonToProduct
        (chartData f).commonToProduct_projection.symm := by
  apply pullback.hom_ext
  · change _ ≫ graphSourceProductFst f = _
    simp only [Category.assoc, graphClosureEmbedding_fst,
      commonToGraphClosure_π, pullback.lift_fst]
  · change _ ≫ graphSourceProductSnd f = _
    simp only [Category.assoc, graphClosureEmbedding_snd,
      commonToGraphClosure_toProduct, pullback.lift_snd]

end FLT.Mazur.Chow
