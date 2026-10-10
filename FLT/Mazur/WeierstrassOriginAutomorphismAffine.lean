/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricOpenFactorization
public import FLT.Mazur.WeierstrassAffinePointNonzero

/-!
# Restrict origin-preserving automorphisms to the actual affine chart

The affine chart is stable under every automorphism over the coefficient base
fixing the origin. Geometric points detect the open containment only; the
resulting restriction is an equality of actual scheme morphisms over arbitrary rings.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)
  (e : integralCurve W ≅ integralCurve W)
  (hb : e.hom ≫ integralCurveStructure W = integralCurveStructure W)
  (hz : integralCurveZero W ≫ e.hom = integralCurveZero W)

include hΔ hb hz in
/-- An origin-preserving automorphism sends every field-valued affine point to the affine chart. -/
theorem originAut_affine_field (K : Type) [Field K]
    (p : Spec (.of K) ⟶ chartScheme W 2) :
    ∃ q : Spec (.of K) ⟶ chartScheme W 2,
      q ≫ integralCurveChart W 2 = p ≫ integralCurveChart W 2 ≫ e.hom := by
  obtain ⟨r, hr⟩ := Spec.map_surjective (p ≫ chartStructure W 2)
  let _ : Algebra R K := r.hom.toAlgebra
  have hp : p ≫ chartStructure W 2 =
      Spec.map (CommRingCat.ofHom (algebraMap R K)) := hr.symm
  let P : integralGroupFieldPoints (K := K) W hΔ :=
    Over.homMk (p ≫ integralCurveChart W 2 ≫ e.hom) (by
      change (p ≫ integralCurveChart W 2 ≫ e.hom) ≫ integralCurveStructure W = _
      rw [Category.assoc, Category.assoc, hb, integralCurveChart_structure]
      exact hp)
  apply nonzeroPoint_factor W hΔ P
  intro hP
  have he := congrArg Over.Hom.left hP
  change p ≫ integralCurveChart W 2 ≫ e.hom =
    Spec.map (CommRingCat.ofHom (algebraMap R K)) ≫ integralCurveZero W at he
  apply affine_chart_point_ne_zero W p hp
  apply (cancel_mono e.hom).mp
  simpa only [Category.assoc, hz] using he

include hΔ hb hz in
/-- The original affine open is stable, without reducedness assumptions on the base. -/
theorem originAut_affine_range :
    Set.range (integralCurveChart W 2 ≫ e.hom) ⊆ Set.range (integralCurveChart W 2) :=
  GeometricOpenFactorization.range_subset _ _
    (fun K _ _ p ↦ originAut_affine_field W hΔ e hb hz K p)

/-- Restrict the actual scheme automorphism to its original affine chart. -/
def originAutAffineHom : chartScheme W 2 ⟶ chartScheme W 2 :=
  IsOpenImmersion.lift (integralCurveChart W 2) (integralCurveChart W 2 ≫ e.hom)
    (originAut_affine_range W hΔ e hb hz)

/-- Restriction intertwines the original automorphism and original chart inclusion. -/
@[reassoc (attr := simp)] theorem originAutAffineHom_inclusion :
    originAutAffineHom W hΔ e hb hz ≫ integralCurveChart W 2 =
      integralCurveChart W 2 ≫ e.hom := IsOpenImmersion.lift_fac _ _ _

/-- The restricted map retains the actual coefficient morphism. -/
@[reassoc] theorem originAutAffineHom_base :
    originAutAffineHom W hΔ e hb hz ≫ chartStructure W 2 = chartStructure W 2 := by
  rw [← integralCurveChart_structure, ← Category.assoc, originAutAffineHom_inclusion,
    Category.assoc, hb]

include hb in
/-- The inverse automorphism fixes the same coefficient morphism. -/
theorem originAut_inverse_base :
    e.inv ≫ integralCurveStructure W = integralCurveStructure W := by
  calc
    _ = e.inv ≫ (e.hom ≫ integralCurveStructure W) := congrArg (e.inv ≫ ·) hb.symm
    _ = _ := e.inv_hom_id_assoc _

include hz in
/-- The inverse automorphism fixes the original zero section. -/
theorem originAut_inverse_zero :
    integralCurveZero W ≫ e.inv = integralCurveZero W := by
  calc
    _ = (integralCurveZero W ≫ e.hom) ≫ e.inv := congrArg (· ≫ e.inv) hz.symm
    _ = _ := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]

/-- The restricted scheme map is an automorphism of the actual affine chart. -/
def originAutAffineIso : chartScheme W 2 ≅ chartScheme W 2 where
  hom := originAutAffineHom W hΔ e hb hz
  inv := originAutAffineHom W hΔ e.symm
    (originAut_inverse_base W e hb) (originAut_inverse_zero W e hz)
  hom_inv_id := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simp only [Category.assoc, originAutAffineHom_inclusion, Iso.symm_hom,
      originAutAffineHom_inclusion_assoc, e.hom_inv_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    apply (cancel_mono (integralCurveChart W 2)).mp
    simp only [Category.assoc, originAutAffineHom_inclusion, Iso.symm_hom,
      originAutAffineHom_inclusion_assoc, e.inv_hom_id, Category.comp_id, Category.id_comp]

end FLT.Mazur.WeierstrassIntegralChart
