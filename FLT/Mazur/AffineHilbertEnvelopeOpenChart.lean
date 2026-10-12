/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertEnvelopeQuotient
public import FLT.Mazur.AffineHilbertRestrictedOpenImmersion

/-!
# Constructed affine charts in the original Hilbert invariant locally ringed space

The full-envelope affine quotient embeds openly into the ORIGINAL unrestricted
invariant quotient. Its source equation is the original restricted projection.
The existence of a covering family satisfying the full-envelope condition is
still a separate geometric construction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom] [Surjective V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left] [IsIso (toEnvelope f hL d V c k).left]
local notation "e" => variableChartEquivalenceRelation f hL d V c
local notation "a" => equivalence f hL d V c k

/-- The constructed affine spectrum maps into the ORIGINAL invariant locally ringed quotient. -/
def fullEnvelopeOpenChart : (fullEnvelopeScheme f hL d V c k).toLocallyRingedSpace ⟶
    invariantLocallyRingedSpace e :=
  (fullEnvelopeInvariantQuotientIso f hL d V c k).inv ≫
    restrictedInvariantQuotientMap f hL d V c k

/-- The constructed affine chart is an open immersion into the original quotient. -/
instance fullEnvelopeOpenChart_isOpenImmersion :
    LocallyRingedSpace.IsOpenImmersion (fullEnvelopeOpenChart f hL d V c k) := by
  let _ := restrictedInvariantQuotientMap_isOpenImmersion f hL d V c k
  unfold fullEnvelopeOpenChart
  infer_instance

omit [IsOpenImmersion k.left] in
/-- Its source equation is the ORIGINAL parameter inclusion and invariant quotient projection. -/
@[reassoc]
theorem fullEnvelopeOpenChart_source :
    (fullEnvelopeProjection f hL d V c k).toLRSHom ≫ fullEnvelopeOpenChart f hL d V c k =
      k.left.toLRSHom ≫ invariantLocallyRingedProjection e := by
  rw [← fullEnvelopeInvariantQuotientIso_projection, fullEnvelopeOpenChart,
    Category.assoc, Iso.hom_inv_id_assoc, restrictedInvariantQuotientMap_projection]

omit [IsOpenImmersion k.left] in
/-- Every original restricted source point belongs to the constructed affine chart image. -/
theorem fullEnvelopeOpenChart_projection (x : A.left) :
    (fullEnvelopeOpenChart f hL d V c k).base (fullEnvelopeProjection f hL d V c k x) =
      projection e (k.left x) := by
  have h := congrArg (fun g ↦ g.base) (fullEnvelopeOpenChart_source f hL d V c k)
  rw [LocallyRingedSpace.comp_base, LocallyRingedSpace.comp_base,
    invariantLocallyRingedProjection_base] at h
  exact congrArg (fun g ↦ g x) h

omit [IsOpenImmersion k.left] in
/-- The constructed chart retains the ORIGINAL quotient structural map to Spec R. -/
theorem fullEnvelopeOpenChart_base :
    fullEnvelopeOpenChart f hL d V c k ≫ invariantLocallyRingedBaseMap e =
      (fullEnvelopeBase f hL d V c k).toLRSHom := by
  rw [fullEnvelopeOpenChart, Category.assoc]
  apply (cancel_epi (fullEnvelopeInvariantQuotientIso f hL d V c k).hom).mp
  rw [Iso.hom_inv_id_assoc, fullEnvelopeInvariantQuotientIso_base]
  let _ : Epi (invariantLocallyRingedProjection a) := by
    unfold invariantLocallyRingedProjection locallyRingedProjection
    infer_instance
  apply (cancel_epi (invariantLocallyRingedProjection a)).mp
  rw [← Category.assoc, restrictedInvariantQuotientMap_projection, Category.assoc,
    invariantLocallyRingedProjection_baseMap, invariantLocallyRingedProjection_baseMap]
  exact congrArg Scheme.Hom.toLRSHom k.w

end FLT.Mazur.HilbertChart.AffineRestriction
