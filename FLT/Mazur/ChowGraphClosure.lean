/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ChowProjectiveProduct
public import FLT.Mazur.ChowSourceClosure

/-!
# The Chow graph closure over a field

Starting with the constructed chart data, take the graph of the common-open
map to the finite projective product over the source closure. Its actual
scheme-theoretic image gives a proper surjective modification of the original
source. The common-open factorization and the map to the projective product
are retained for the subsequent restriction comparison.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace

universe u

set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.Chow

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
  [IsSeparated f] [LocallyOfFiniteType f] [QuasiCompact f]

/-- The structure morphism of the constructed source closure. -/
def graphSourceProjection : (chartData f).sourceClosure ⟶ Spec (.of k) :=
  (chartData f).sourceClosureι ≫ f

/-- The ambient relative product for the graph closure. -/
def graphAmbient : Scheme.{u} :=
  pullback (graphSourceProjection f) (chartData f).projectiveProductProjection

/-- The first ambient projection lands in the scheme-theoretic source closure. -/
def graphAmbientFst : graphAmbient f ⟶ (chartData f).sourceClosure :=
  pullback.fst _ _

/-- The second ambient projection lands in the finite projective product. -/
def graphAmbientSnd : graphAmbient f ⟶ (chartData f).projectiveProduct :=
  pullback.snd _ _

@[reassoc]
lemma graphAmbient_condition :
    graphAmbientFst f ≫ graphSourceProjection f =
      graphAmbientSnd f ≫ (chartData f).projectiveProductProjection := pullback.condition

/-- The first projection is a base change of the proper product projection. -/
instance graphAmbientFst_isProper : IsProper (graphAmbientFst f) := by
  dsimp [graphAmbientFst, graphAmbient]
  infer_instance

/-- The common open maps to the ambient product by its source and chart tuples. -/
def commonToGraphAmbient : (chartData f).common.toScheme ⟶ graphAmbient f :=
  pullback.lift (chartData f).commonToSourceClosure (chartData f).commonToProduct
    (by simp [graphSourceProjection])

@[reassoc (attr := simp)]
lemma commonToGraphAmbient_fst :
    commonToGraphAmbient f ≫ graphAmbientFst f = (chartData f).commonToSourceClosure :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
lemma commonToGraphAmbient_snd :
    commonToGraphAmbient f ≫ graphAmbientSnd f = (chartData f).commonToProduct :=
  pullback.lift_snd _ _ _

/-- Cancellation of the first projection proves the graph map is an immersion. -/
instance commonToGraphAmbient_isImmersion : IsImmersion (commonToGraphAmbient f) := by
  have : IsImmersion (commonToGraphAmbient f ≫ graphAmbientFst f) := by
    rw [commonToGraphAmbient_fst]
    infer_instance
  exact IsImmersion.of_comp _ (graphAmbientFst f)

/-- Finite type over the field makes the common open noetherian. -/
instance commonToGraphAmbient_quasiCompact : QuasiCompact (commonToGraphAmbient f) := by
  let _noetherian := source_isNoetherian f
  have : NoetherianSpace (chartData f).common.toScheme :=
    NoetherianSpace.set ((chartData f).common : Set X)
  exact quasiCompact_of_noetherianSpace_source _

/-- The graph modification is the actual scheme-theoretic image in the ambient product. -/
def graphClosure : Scheme.{u} := (commonToGraphAmbient f).image

/-- The canonical closed immersion of the graph closure into the ambient product. -/
def graphClosureι : graphClosure f ⟶ graphAmbient f := (commonToGraphAmbient f).imageι

instance graphClosureι_isClosedImmersion : IsClosedImmersion (graphClosureι f) := by
  dsimp [graphClosureι]
  infer_instance

/-- The modification map to the original source. -/
def graphClosureπ : graphClosure f ⟶ X :=
  graphClosureι f ≫ graphAmbientFst f ≫ (chartData f).sourceClosureι

/-- The retained map from the graph closure to the projective product. -/
def graphClosureToProduct : graphClosure f ⟶ (chartData f).projectiveProduct :=
  graphClosureι f ≫ graphAmbientSnd f

/-- The common open factors canonically through the graph closure. -/
def commonToGraphClosure : (chartData f).common.toScheme ⟶ graphClosure f :=
  (commonToGraphAmbient f).toImage

@[reassoc (attr := simp)]
lemma commonToGraphClosure_ι :
    commonToGraphClosure f ≫ graphClosureι f = commonToGraphAmbient f :=
  (commonToGraphAmbient f).toImage_imageι

@[reassoc (attr := simp)]
lemma commonToGraphClosure_π :
    commonToGraphClosure f ≫ graphClosureπ f = (chartData f).common.ι := by
  simp [graphClosureπ, ← Category.assoc]

@[reassoc (attr := simp)]
lemma commonToGraphClosure_toProduct :
    commonToGraphClosure f ≫ graphClosureToProduct f = (chartData f).commonToProduct := by
  simp [graphClosureToProduct, ← Category.assoc]

/-- Both retained maps have the same structure morphism over the field. -/
@[reassoc]
lemma graphClosureToProduct_projection :
    graphClosureToProduct f ≫ (chartData f).projectiveProductProjection = graphClosureπ f ≫ f := by
  simp only [graphClosureToProduct, graphClosureπ, Category.assoc]
  rw [← graphAmbient_condition, graphSourceProjection]

/-- The common open is an open subscheme of its graph closure. -/
instance commonToGraphClosure_isOpenImmersion : IsOpenImmersion (commonToGraphClosure f) := by
  dsimp [commonToGraphClosure]
  infer_instance

/-- The graph closure retains exactly the scheme-theoretic closure of the common open. -/
instance commonToGraphClosure_schemeTheoreticallyDominant :
    IsSchemeTheoreticallyDominant (commonToGraphClosure f) :=
  toImage_schemeTheoreticallyDominant (commonToGraphAmbient f)

/-- Closed immersion, proper base change, and the source closure give properness. -/
instance graphClosureπ_isProper : IsProper (graphClosureπ f) := by
  dsimp [graphClosureπ]
  infer_instance

/-- Every point of the original common open is in the image of the modification. -/
lemma common_subset_range_graphClosureπ :
    ((chartData f).common : Set X) ⊆ Set.range (graphClosureπ f) := by
  intro x hx
  refine ⟨commonToGraphClosure f ⟨x, hx⟩, ?_⟩
  change (commonToGraphClosure f ≫ graphClosureπ f) ⟨x, hx⟩ = x
  rw [commonToGraphClosure_π]
  rfl

/-- Properness makes the image closed; it contains the dense common open. -/
lemma graphClosureπ_surjective : Function.Surjective (graphClosureπ f) := by
  rw [← Set.range_eq_univ]
  apply Set.eq_univ_of_univ_subset
  rw [← (chartData f).common_dense.closure_eq]
  exact closure_minimal (common_subset_range_graphClosureπ f)
    (graphClosureπ f).isClosedMap.isClosed_range

end FLT.Mazur.Chow
