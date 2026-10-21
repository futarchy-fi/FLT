/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarImageQuotient
public import FLT.Mazur.SchemeEffectiveEpiSections
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Effectivity of the constructed exact scalar image

Faithful flatness of the actual kernel lift makes the constructed image
projection effective. Flatness and integrality suffice, since the kernel
lift is already injective. These are properties of a fixed constructed map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarImageQuotient
open SchemeScalarPrincipalNeighborhood FlatScalarFunctionPushout SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {S : Type} [CommRing S] {X : Scheme.{0}} [IsAffine X]
  (b : X ⟶ Spec (.of S))

/-- Faithful flatness of the exact kernel lift constructs an effective image projection. -/
theorem projection_effectiveEpi
    (h : (RingHom.kerLift (scalarMap b)).FaithfullyFlat) : EffectiveEpi (projection b) := by
  let k := CommRingCat.ofHom (RingHom.kerLift (scalarMap b))
  have hk : Flat (Spec.map k) ∧ Surjective (Spec.map k) :=
    (flat_and_surjective_SpecMap_iff k).mpr h
  let _ := hk.1
  let _ := hk.2
  change EffectiveEpi (X.toSpecΓ ≫ Spec.map k)
  infer_instance

omit [IsAffine X] in
/-- Flat integral scalar-image coordinates are faithfully flat without extra prime coverage. -/
theorem image_faithfullyFlat_of_flat_integral
    (hf : (RingHom.kerLift (scalarMap b)).Flat)
    (hi : (RingHom.kerLift (scalarMap b)).IsIntegral) :
    (RingHom.kerLift (scalarMap b)).FaithfullyFlat := by
  exact RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mpr
    ⟨hf, hi.comap_surjective (RingHom.kerLift_injective _)⟩

/-- Flat integral full image coordinates give effective descent on the constructed image. -/
theorem projection_effectiveEpi_of_flat_integral
    (hf : (RingHom.kerLift (scalarMap b)).Flat)
    (hi : (RingHom.kerLift (scalarMap b)).IsIntegral) : EffectiveEpi (projection b) :=
  projection_effectiveEpi b (image_faithfullyFlat_of_flat_integral b hf hi)

omit [IsAffine X] in
/-- Full kernel-pair compatibility gives a unique scalar in the exact image quotient. -/
theorem existsUnique_image_scalar [EffectiveEpi (projection b)] (t : Γ(X, ⊤))
    (ht : (pullback.fst (projection b) (projection b)).appTop t =
      (pullback.snd (projection b) (projection b)).appTop t) :
    ∃! s : Scalars b, scalarMap (projection b) s = t := by
  obtain ⟨v, hv, _⟩ := sections_existsUnique
    (IsPullback.of_hasPullback (projection b) (projection b)) t ht
  let e := (Scheme.ΓSpecIso (.of (Scalars b))).commRingCatIsoToRingEquiv
  refine ⟨e v, ?_, ?_⟩
  · change (projection b).appTop (e.symm (e v)) = t
    rw [e.symm_apply_apply, hv]
  · intro s hs
    apply projection_coefficients_injective b
    exact hs.trans (by
      change t = (projection b).appTop (e.symm (e v))
      rw [e.symm_apply_apply, hv])

end FLT.Mazur.SchemeScalarImageQuotient
