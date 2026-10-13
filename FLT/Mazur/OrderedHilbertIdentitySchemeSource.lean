/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OrderedHilbertIdentityQuotientCover

/-!
# One constructed scheme source covering the original invariant quotient

Take the actual scheme coproduct of the effective affine sources. Preservation
of coproducts by the locally ringed space functor assembles their original
quotient maps. The resulting map is surjective on every original orbit;
effectivity of its full original relation remains a separate descent task.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.OrderedHilbertIdentitySchemeSource
open HilbertChart CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
local notation "Q" => OrderedHilbertIdentityQuotientCover.source f hL
local notation "j" => OrderedHilbertIdentityQuotientCover.toOriginal f hL
local notation "e" => smoothHilbertEquivalenceRelation f hL

/-- One scheme, the disjoint union of the constructed effective affine sources. -/
def source : Scheme := ∐ Q

/-- The original quotient maps assemble on the actual scheme coproduct. -/
def toOriginal : (source f hL).toLocallyRingedSpace ⟶ invariantLocallyRingedSpace e :=
  inv (sigmaComparison Scheme.forgetToLocallyRingedSpace Q) ≫ Sigma.desc j

/-- Each original component map is recovered literally on its unchanged affine component. -/
@[reassoc]
theorem component_toOriginal (x : (smoothHilbertSource f).left) :
    (Sigma.ι Q x).toLRSHom ≫ toOriginal f hL = j x := by
  change Scheme.forgetToLocallyRingedSpace.map (Sigma.ι Q x) ≫
    inv (sigmaComparison Scheme.forgetToLocallyRingedSpace Q) ≫ Sigma.desc j = _
  rw [map_ι_comp_inv_sigmaComparison_assoc, Sigma.ι_comp_desc]

/-- The assembled map retains each component point exactly. -/
theorem component_toOriginal_apply (x : (smoothHilbertSource f).left) (y : Q x) :
    (toOriginal f hL).base (Sigma.ι Q x y) = (j x).base y := by
  have hh := congrArg (fun g ↦ g.base) (component_toOriginal f hL x)
  rw [LocallyRingedSpace.comp_base] at hh
  exact congrArg (fun g ↦ g y) hh

/-- The assembled map is topologically open on the original quotient. -/
theorem toOriginal_isOpenMap : IsOpenMap (toOriginal f hL).base := by
  apply IsOpenMap.of_comp (sigmaMk Q).continuous (sigmaMk Q).surjective
  rw [isOpenMap_sigma]
  intro x
  simpa only [Function.comp_apply, sigmaMk_mk, component_toOriginal_apply] using
    OrderedHilbertIdentityQuotientCover.toOriginal_isOpenMap f hL x

/-- The single constructed scheme maps onto the entire ORIGINAL quotient. -/
theorem toOriginal_surjective : Function.Surjective (toOriginal f hL).base := by
  intro z
  obtain ⟨x, y, hy⟩ := OrderedHilbertIdentityQuotientCover.covers f hL z
  refine ⟨Sigma.ι Q x y, ?_⟩
  have hh := congrArg (fun g ↦ g.base) (component_toOriginal f hL x)
  rw [LocallyRingedSpace.comp_base] at hh
  exact (congrArg (fun g ↦ g y) hh).trans hy

/-- The assembled source retains the ORIGINAL coefficient base through its quotient map. -/
def base : source f hL ⟶ Spec (.of R) :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.preimage
    (toOriginal f hL ≫ invariantLocallyRingedBaseMap e)

/-- The coefficient square is an actual locally ringed morphism equality. -/
theorem base_eq : (base f hL).toLRSHom =
    toOriginal f hL ≫ invariantLocallyRingedBaseMap e :=
  Scheme.fullyFaithfulForgetToLocallyRingedSpace.map_preimage _

end FLT.Mazur.OrderedHilbertIdentitySchemeSource
