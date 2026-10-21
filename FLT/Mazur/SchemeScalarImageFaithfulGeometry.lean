/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarImageGeometry
public import FLT.Mazur.SchemeScalarImageDescent

/-!
# Faithful flatness of the exact image from its geometry

For a full affine source, the exact image coefficients are faithfully flat
precisely when its projection is flat and surjective. Closedness of the
original scalar image supplies the latter without radicalizing the kernel.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarImageQuotient
open FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
variable {S : Type} [CommRing S] {X : Scheme.{0}} [IsAffine X]
  (b : X ⟶ Spec (.of S))

/-- Geometric flatness and coverage detect faithful flatness of the exact kernel lift. -/
theorem image_faithfullyFlat_iff :
    (RingHom.kerLift (scalarMap b)).FaithfullyFlat ↔
      Flat (projection b) ∧ Surjective (projection b) := by
  have he : Spec.map (CommRingCat.ofHom (RingHom.kerLift (scalarMap b))) =
      X.isoSpec.inv ≫ projection b := by
    change _ = X.isoSpec.inv ≫ (X.toSpecΓ ≫ _)
    simp only [← Scheme.isoSpec_hom, Iso.inv_hom_id_assoc]
  have hi := flat_and_surjective_SpecMap_iff (CommRingCat.ofHom
    (RingHom.kerLift (scalarMap b)))
  simp only [CommRingCat.hom_ofHom] at hi
  rw [← hi, he]
  constructor
  · rintro ⟨hf, hs⟩
    let _ := hf
    let _ := hs
    have hb : projection b = X.isoSpec.hom ≫ (X.isoSpec.inv ≫ projection b) := by
      simp only [Iso.hom_inv_id_assoc]
    rw [hb]
    exact ⟨inferInstance, inferInstance⟩
  · rintro ⟨hf, hs⟩
    let _ := hf
    let _ := hs
    exact ⟨inferInstance, inferInstance⟩

/-- Flat image projection and closed original range suffice for exact coefficient descent. -/
theorem image_faithfullyFlat_of_flat_closed [Flat (projection b)]
    (hc : IsClosed (Set.range b)) : (RingHom.kerLift (scalarMap b)).FaithfullyFlat :=
  (image_faithfullyFlat_iff b).mpr
    ⟨inferInstance, projection_surjective_of_isClosed_range b hc⟩

/-- Integrality supplies coverage, leaving only flatness of the full image projection. -/
theorem image_faithfullyFlat_of_flat_integral_morphism [Flat (projection b)]
    [IsIntegralHom b] : (RingHom.kerLift (scalarMap b)).FaithfullyFlat :=
  image_faithfullyFlat_of_flat_closed b b.isClosedMap.isClosed_range

end FLT.Mazur.SchemeScalarImageQuotient
