/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalLocalizationSquare

/-!
# Coherent principal-open intersections

Principal-open inclusions compose exactly, and the model obtained by
inverting a product is the scheme-theoretic intersection of the two models.
These statements apply at every finite-relation stage and at the limit.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.PrincipalLocalizationSquare

universe u

variable {A : Type u} [CommRing A]

/-- The canonical inclusion between nested principal opens. -/
def openInclusion {r s : A} (h : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r) :
    Spec (.of (Localization.Away s)) ⟶ Spec (.of (Localization.Away r)) :=
  IsOpenImmersion.lift (inclusion r) (inclusion s) (by
    change (inclusion s).opensRange ≤ (inclusion r).opensRange
    rwa [inclusion_opensRange, inclusion_opensRange])

/-- Nested principal-open inclusions retain the original map into the chart. -/
@[reassoc (attr := simp)] theorem openInclusion_fac {r s : A}
    (h : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r) :
    openInclusion h ≫ inclusion r = inclusion s :=
  IsOpenImmersion.lift_fac _ _ _

/-- Each map between nested principal opens is itself an open immersion. -/
instance openInclusion_isOpenImmersion {r s : A}
    (h : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r) :
    IsOpenImmersion (openInclusion h) := by
  have : IsOpenImmersion (openInclusion h ≫ inclusion r) := by
    rw [openInclusion_fac]
    infer_instance
  exact IsOpenImmersion.of_comp (openInclusion h) (inclusion r)

/-- All paths of nested principal-open inclusions commute. -/
theorem openInclusion_comp {r s t : A}
    (h : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r)
    (k : PrimeSpectrum.basicOpen t ≤ PrimeSpectrum.basicOpen s) :
    openInclusion k ≫ openInclusion h = openInclusion (k.trans h) := by
  rw [← cancel_mono (inclusion r)]
  simp only [Category.assoc, openInclusion_fac]

/-- Localizing at a product constructs the actual overlap, as a pullback of schemes. -/
theorem product_isPullback (r s : A) :
    IsPullback (openInclusion (PrimeSpectrum.basicOpen_mul_le_left r s))
      (openInclusion (PrimeSpectrum.basicOpen_mul_le_right r s)) (inclusion r) (inclusion s) := by
  apply IsOpenImmersion.isPullback
  · simp only [openInclusion_fac]
  · apply (inclusion s).image_injective
    dsimp only
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, ← Scheme.Hom.opensRange_comp]
    simp only [openInclusion_fac, inclusion_opensRange, PrimeSpectrum.basicOpen_mul]
    change PrimeSpectrum.basicOpen s ⊓ PrimeSpectrum.basicOpen r =
      PrimeSpectrum.basicOpen r ⊓ PrimeSpectrum.basicOpen s
    exact inf_comm _ _

/-- Inclusions between principal opens commute with arbitrary changes of ring. -/
theorem restriction_openInclusion {B : Type u} [CommRing B] (f : A →+* B) {r s : A}
    (h : PrimeSpectrum.basicOpen s ≤ PrimeSpectrum.basicOpen r)
    (hf : PrimeSpectrum.basicOpen (f s) ≤ PrimeSpectrum.basicOpen (f r)) :
    restriction f s ≫ openInclusion h = openInclusion hf ≫ restriction f r := by
  rw [← cancel_mono (inclusion r)]
  simp only [Category.assoc, openInclusion_fac, ← condition, openInclusion_fac_assoc]

end FLT.Mazur.PrincipalLocalizationSquare
