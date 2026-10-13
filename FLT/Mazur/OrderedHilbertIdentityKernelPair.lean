/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertIdentityRelationLift

/-!
# The full original Picard kernel pair of the constructed source

The relation's universal lifting theorem gives the actual presheaf pullback.
This keeps the original Picard sheaf and arbitrary tests in the statement.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertIdentityOriginalRelation
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
open OrderedHilbertAffineEtaleTestCover OrderedHilbertFaithfulTestCover AffineRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "T" => smoothHilbertSource f
local notation "s" => smoothHilbertSourceSection f hL
local notation "E" => fun x ↦ Sigma.fst (Sigma.snd (chartData f hL T s x))
local notation "d" => fun x ↦ Prod.snd (Sigma.fst (chartData f hL T s x))
local notation "c" => fun x ↦ chartClass f hL T s x
local notation "A" => OrderedHilbertIdentityOriginalSection.test f hL
local notation "k" => OrderedHilbertIdentityOriginalSection.parameter f hL
local notation "U" => OrderedHilbertIdentityOriginalSection.sourceTest f hL
local notation "sU" => OrderedHilbertIdentityOriginalSection.sourceSection f hL
local notation "sA" => OrderedHilbertIdentityOriginalSection.sectionAt f hL
local notation "ι" => OrderedHilbertIdentityOriginalSection.component f hL

/-- The constructed source maps to the ORIGINAL Picard sheaf by its original section. -/
def sourceMap : uliftYoneda.{1}.obj U ⟶ (relativeFppfSheaf f).obj ⋙ forget CommGrpCat :=
  uliftYonedaEquiv.symm sU

/-- The entire original relation is the full kernel pair on every original test. -/
theorem isPullback :
    IsPullback (uliftYoneda.{1}.map (fst f hL)) (uliftYoneda.{1}.map (snd f hL))
      (sourceMap f hL) (sourceMap f hL) := by
  apply IsPullback.of_forall_isPullback_app
  intro W
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · apply ConcreteCategory.hom_ext
    intro z
    change (relativeFppfSheaf f).obj.map (z.down ≫ fst f hL).op sU =
      (relativeFppfSheaf f).obj.map (z.down ≫ snd f hL).op sU
    simp only [op_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    rw [equal_class]
  · intro a b hab
    apply ULift.ext
    exact hom_ext f hL (congrArg ULift.down hab.1) (congrArg ULift.down hab.2)
  · intro a b hab
    obtain ⟨z, hz, _⟩ := lift f hL a.down b.down hab
    exact ⟨ULift.up z, ULift.ext hz.1, ULift.ext hz.2⟩

end FLT.Mazur.OrderedHilbertIdentityOriginalRelation
