/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.VariableHilbertDescendedKernel
public import FLT.Mazur.RelativeRelationFppfInvariantQuotient
public import Mathlib.CategoryTheory.EffectiveEpi.Comp

/-!
# A refined effective model gives the full original scheme quotient

The original projection and its full scheme kernel pair are constructed, and
its scheme coequalizer and invariant locally ringed model agree. The refined
model remains an input: this result does not assert that such models cover.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.VariableHilbertFppfRefinement
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) {V W : Over (Spec (.of R))} (b : W ⟶ V)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  [Flat b.left] [LocallyOfFinitePresentation b.left] [Surjective b.left]
local notation "cW" => CategoryTheory.Functor.map
  (ObjectProperty.FullSubcategory.obj (relativeFppfSheaf f)) (Quiver.Hom.op b) c
local notation "g" => baseMarkedChartChange f b d
local notation "P" => variableChartRelationFst f hL d V c
local notation "Q" => variableChartRelationSnd f hL d V c
local notation "P₁" => variableChartRelationFst f hL d W cW
local notation "Q₁" => variableChartRelationSnd f hL d W cW
local notation "e" => variableChartEquivalenceRelation f hL d V c
local notation "e₁" => variableChartEquivalenceRelation f hL d W cW
variable {Z : Over (Spec (.of R))} (π : variableHilbertTest f d W ⟶ Z)
  (H : IsPullback
    (variableChartRelationFst f hL d W ((relativeFppfSheaf f).obj.map b.op c))
    (variableChartRelationSnd f hL d W ((relativeFppfSheaf f).obj.map b.op c)) π π)
  [Flat π.left] [LocallyOfFinitePresentation π.left] [Surjective π.left]
local notation "D" => descendedProjection f hL d b c π H.w

/-- The original descended scheme projection is effective epimorphic. -/
theorem descendedProjection_effectiveEpi : EffectiveEpi (D).left := by
  have he : (g).left ≫ (D).left = π.left :=
    congrArg Over.Hom.left (descendedProjection_source f hL d b c π H.w)
  let _ : EffectiveEpi ((g).left ≫ (D).left) := he.symm ▸ inferInstance
  exact effectiveEpi_of_effectiveEpi_epi_comp (D).left (g).left

/-- The original full relation has this actual scheme as its scheme coequalizer. -/
def descendedCoforkIsColimit : IsColimit (Cofork.ofπ (D).left
    (congrArg Over.Hom.left (descendedProjection_condition f hL d b c π H.w))) :=
  let _ := descendedProjection_effectiveEpi f hL d b c π H
  isColimitCoforkOfEffectiveEpi (D).left _
    ((descendedProjection_isPullback f hL d b c π H).map (Over.forget _)).isLimit

/-- Every invariant regular function on the full original quotient belongs to the model. -/
def descendedInvariantIso : invariantLocallyRingedSpace e ≅ Z.left.toLocallyRingedSpace :=
  (invariantIso f hL d b c).symm ≪≫ fppfInvariantQuotientIso e₁ π H

/-- The invariant scheme model has precisely the constructed original projection. -/
@[reassoc]
theorem descendedInvariantIso_projection :
    invariantLocallyRingedProjection e ≫ (descendedInvariantIso f hL d b c π H).hom =
      (D).left.toLRSHom := by
  let _ := RelativeFppfLocallyRingedCover.epi g
  apply (cancel_epi (g).left.toLRSHom).mp
  dsimp only [descendedInvariantIso, Iso.trans_hom, Iso.symm_hom]
  rw [← Category.assoc, ← invariantIso_source, Category.assoc,
    Iso.hom_inv_id_assoc, fppfInvariantQuotientIso_projection,
    ← Scheme.Hom.comp_toLRSHom, ← Over.comp_left, descendedProjection_source]

/-- The full invariant structure sheaf preserves its original coefficient morphism. -/
theorem descendedInvariantIso_base :
    (descendedInvariantIso f hL d b c π H).hom ≫ Z.hom.toLRSHom =
      invariantLocallyRingedBaseMap e := by
  dsimp only [descendedInvariantIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, fppfInvariantQuotientIso_baseMap, ← invariantIso_base f hL d b c,
    Iso.inv_hom_id_assoc]

/-- The coequalizer presentation also identifies the entire locally ringed quotient. -/
def descendedLocallyRingedIso : locallyRingedQuotient (p := P) (q := Q) ≅
    Z.left.toLocallyRingedSpace :=
  invariantLocallyRingedIso e ≪≫ descendedInvariantIso f hL d b c π H

end FLT.Mazur.VariableHilbertFppfRefinement
