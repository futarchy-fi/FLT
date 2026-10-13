/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFppfSchemeCover
public import FLT.Mazur.VariableHilbertRefinementQuotient
public import FLT.Mazur.SchemeFlatFamilyReflection

/-!
# Descending an effective refined Hilbert projection to the original source

The input projection belongs to the refined full parameter relation. Its
actual scheme morphism descends to the original source; both independent
endpoints of the original relation are coequalized. No original quotient
projection or translation-base descent compatibility is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.VariableHilbertFppfRefinement
open HilbertChart CartierAbel SchemePicard FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "g" => baseMarkedChartChange f b d
local notation "P" => variableChartRelationFst f hL d V c
local notation "Q" => variableChartRelationSnd f hL d V c
local notation "P₁" => variableChartRelationFst f hL d W cW
local notation "Q₁" => variableChartRelationSnd f hL d W cW
variable {Z : Over (Spec (.of R))} (π : variableHilbertTest f d W ⟶ Z)
  (hπ : variableChartRelationFst f hL d W ((relativeFppfSheaf f).obj.map b.op c) ≫ π =
    variableChartRelationSnd f hL d W ((relativeFppfSheaf f).obj.map b.op c) ≫ π)

include hπ in
/-- Full refined compatibility implies compatibility on the source cover's kernel pair. -/
theorem refinedProjection_kernel_condition :
    pullback.fst g g ≫ π = pullback.snd g g ≫ π := by
  rw [← kernelToRelation_fst f hL d b c, ← kernelToRelation_snd f hL d b c]
  simpa only [Category.assoc] using congrArg (fun k ↦ kernelToRelation f hL d b c ≫ k) hπ

variable [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left]

/-- The actual projection from the original parameter source is constructed by scheme descent. -/
def descendedProjection : variableHilbertTest f d V ⟶ Z :=
  RelativeFppfSchemeCover.descend g π (refinedProjection_kernel_condition f hL d b c π hπ)

/-- The refined source recovers its prescribed projection exactly. -/
@[reassoc]
theorem descendedProjection_source : g ≫ descendedProjection f hL d b c π hπ = π :=
  RelativeFppfSchemeCover.descend_source _ _ _

/-- Descent recovers the projection uniquely as a scheme morphism over the original base. -/
theorem descendedProjection_unique (a : variableHilbertTest f d V ⟶ Z) (ha : g ≫ a = π) :
    a = descendedProjection f hL d b c π hπ :=
  RelativeFppfSchemeCover.descend_unique _ _ _ a ha

/-- The entire original relation, including mixed translation endpoints, is coequalized. -/
theorem descendedProjection_condition :
    P ≫ descendedProjection f hL d b c π hπ =
      Q ≫ descendedProjection f hL d b c π hπ := by
  apply (Over.forget _).map_injective
  apply (cancel_epi (relationMap f hL d b c).left).mp
  change (relationMap f hL d b c ≫ (P ≫ descendedProjection f hL d b c π hπ)).left =
    (relationMap f hL d b c ≫ (Q ≫ descendedProjection f hL d b c π hπ)).left
  rw [relationMap_fst_assoc, relationMap_snd_assoc,
    descendedProjection_source, hπ]

instance descendedProjection_surjective [Surjective π.left] :
    Surjective (descendedProjection f hL d b c π hπ).left := by
  constructor
  intro z
  obtain ⟨w, hw⟩ := π.left.surjective z
  refine ⟨(g).left w, ?_⟩
  change ((g).left ≫ (descendedProjection f hL d b c π hπ).left) w = z
  rw [← Over.comp_left, descendedProjection_source]
  exact hw

/-- Flatness of the refined projection descends through the actual flat source cover. -/
instance descendedProjection_flat [Flat π.left] :
    Flat (descendedProjection f hL d b c π hπ).left := by
  have he : (g).left ≫ (descendedProjection f hL d b c π hπ).left = π.left :=
    congrArg Over.Hom.left (descendedProjection_source f hL d b c π hπ)
  exact SchemeFlatFamilyReflection.flat_of_family _ (fun _ : Unit ↦ _)
    (fun _ ↦ (g).left) (fun x ↦ ⟨(), (g).left.surjective x⟩)
    (fun _ ↦ he.symm ▸ inferInstanceAs (Flat π.left))

end FLT.Mazur.VariableHilbertFppfRefinement
