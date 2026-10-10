/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPrincipalBaseChangeScalars
public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Base change in principal affine coordinates

The restriction of a spectrum map to a principal open is the spectrum of the
actual map of principal localizations.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable {S : Type u} [CommRing S] (T : Type u) [CommRing T] [Algebra S T]

/-- The preimage of a principal open is the principal open of the image element. -/
theorem principalBaseChange_le (r : S) :
    PrimeSpectrum.basicOpen (algebraMap S T r) ≤
      (Spec.map (CommRingCat.ofHom (algebraMap S T))) ⁻¹ᵁ PrimeSpectrum.basicOpen r :=
  le_rfl

/-- Restriction of the base map to the corresponding principal open subschemes. -/
def principalBaseChangeMorphism (r : S) :
    Scheme.Opens.toScheme (X := Spec (.of T)) (PrimeSpectrum.basicOpen (algebraMap S T r)) ⟶
      Scheme.Opens.toScheme (X := Spec (.of S)) (PrimeSpectrum.basicOpen r) :=
  (Spec.map (CommRingCat.ofHom (algebraMap S T))).resLE _ _ (principalBaseChange_le T r)

/-- Localization coordinates compute the restricted spectrum map exactly. -/
theorem principalBaseChangeMorphism_affine (r : S) :
    (basicOpenIsoSpecAway (R := .of T) (algebraMap S T r)).inv ≫
      principalBaseChangeMorphism T r ≫ (basicOpenIsoSpecAway (R := .of S) r).hom =
    Spec.map (CommRingCat.ofHom (principalBaseChangeMap T r).toRingHom) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))]
  rw [Category.assoc, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap,
    principalBaseChangeMorphism, Scheme.Hom.resLE_comp_ι]
  have ha : (principalBaseChangeMap T r).toRingHom.comp
      (algebraMap S (Localization.Away r)) =
      (algebraMap T (Localization.Away (algebraMap S T r))).comp (algebraMap S T) := by
    apply RingHom.ext
    intro x
    exact (principalBaseChangeMap T r).commutes x
  rw [← Spec.map_comp]
  change _ = Spec.map (CommRingCat.ofHom
    ((principalBaseChangeMap T r).toRingHom.comp (algebraMap S (Localization.Away r))))
  rw [ha]
  change _ = Spec.map (CommRingCat.ofHom (algebraMap S T) ≫
    CommRingCat.ofHom (algebraMap T (Localization.Away (algebraMap S T r))))
  rw [Spec.map_comp, ← basicOpenIsoSpecAway_hom_SpecMap (R := .of T),
    Category.assoc, Iso.inv_hom_id_assoc]

end FLT.Mazur.HilbertChart
