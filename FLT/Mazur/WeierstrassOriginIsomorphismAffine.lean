/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassOriginAutomorphismAffine

/-!
# Affine restriction of origin-preserving isomorphisms between two cubics

An arbitrary base- and origin-preserving scheme isomorphism restricts to the
original affine charts. No coordinate formula for the isomorphism is assumed.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W V : WeierstrassCurve R) (hV : IsUnit V.Δ)
  (e : integralCurve W ≅ integralCurve V)
  (hb : e.hom ≫ integralCurveStructure V = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero V)

include hV hb hz in
/-- Every field-valued affine point remains affine under the arbitrary isomorphism. -/
theorem originIso_affine_field (K : Type) [Field K]
    (p : Spec (.of K) ⟶ chartScheme W 2) :
    ∃ q : Spec (.of K) ⟶ chartScheme V 2,
      q ≫ integralCurveChart V 2 = p ≫ integralCurveChart W 2 ≫ e.hom := by
  obtain ⟨r, hr⟩ := Spec.map_surjective (p ≫ chartStructure W 2)
  let _ : Algebra R K := r.hom.toAlgebra
  have hp : p ≫ chartStructure W 2 =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := hr.symm
  let P : integralGroupFieldPoints (K := K) V hV :=
    Over.homMk (p ≫ integralCurveChart W 2 ≫ e.hom) (by
      change (p ≫ integralCurveChart W 2 ≫ e.hom) ≫ integralCurveStructure V = _
      rw [Category.assoc, Category.assoc, hb, integralCurveChart_structure]
      exact hp)
  apply nonzeroPoint_factor V hV P
  intro hP
  have he := congrArg Over.Hom.left hP
  change p ≫ integralCurveChart W 2 ≫ e.hom =
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ integralCurveZero V at he
  apply affine_chart_point_ne_zero W p hp
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc, hz] using he

include hV hb hz in
/-- The actual affine-open containment follows from the field-point test. -/
theorem originIso_affine_range :
    Set.range (integralCurveChart W 2 ≫ e.hom) ⊆ Set.range (integralCurveChart V 2) :=
  GeometricOpenFactorization.range_subset _ _
    (fun K _ _ p => originIso_affine_field W V hV e hb hz K p)

/-- The isomorphism restricted to the original affine charts. -/
def originIsoAffineHom : chartScheme W 2 ⟶ chartScheme V 2 :=
  IsOpenImmersion.lift (integralCurveChart V 2) (integralCurveChart W 2 ≫ e.hom)
    (originIso_affine_range W V hV e hb hz)

/-- Restriction retains the original scheme morphism. -/
@[reassoc] theorem originIsoAffineHom_inclusion :
    originIsoAffineHom W V hV e hb hz ≫ integralCurveChart V 2 =
      integralCurveChart W 2 ≫ e.hom := IsOpenImmersion.lift_fac _ _ _

/-- Restriction retains the original coefficient map. -/
@[reassoc] theorem originIsoAffineHom_base :
    originIsoAffineHom W V hV e hb hz ≫ chartStructure V 2 = chartStructure W 2 := by
  rw [← integralCurveChart_structure, ← Category.assoc, originIsoAffineHom_inclusion,
    Category.assoc, hb, integralCurveChart_structure]

include hb in
/-- The inverse isomorphism is over the same base. -/
theorem originIso_inverse_base : e.inv ≫ integralCurveStructure W = integralCurveStructure V := by
  rw [← hb, e.inv_hom_id_assoc]

include hz in
/-- The inverse isomorphism sends the target origin to the source origin. -/
theorem originIso_inverse_zero : integralCurveZero V ≫ e.inv = integralCurveZero W := by
  rw [← hz, Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The original affine charts of two smooth cubics are genuinely isomorphic. -/
def originIsoAffineIso (hW : IsUnit W.Δ) : chartScheme W 2 ≅ chartScheme V 2 where
  hom := originIsoAffineHom W V hV e hb hz
  inv := originIsoAffineHom V W hW e.symm
    (originIso_inverse_base W V e hb) (originIso_inverse_zero W V e hz)
  hom_inv_id := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simp only [Category.assoc, originIsoAffineHom_inclusion, Iso.symm_hom,
      originIsoAffineHom_inclusion_assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (integralCurveChart V 2)).mp
    simp only [Category.assoc, originIsoAffineHom_inclusion, Iso.symm_hom,
      originIsoAffineHom_inclusion_assoc, e.inv_hom_id, Category.comp_id, Category.id_comp]

end FLT.Mazur.WeierstrassIntegralChart
