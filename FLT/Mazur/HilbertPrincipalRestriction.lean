/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Restrict

/-!
# Principal restriction in localization coordinates

Restriction between principal open subschemes is the spectrum of the actual
localization algebra map. This lets algebraic compatibility prove scheme gluing.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.HilbertChart

variable {S : Type u} [CommRing S]

set_option backward.isDefEq.respectTransparency false in
/-- Every localization algebra map computes the corresponding principal restriction. -/
theorem principal_restriction_SpecMap (r t : S)
    (h : PrimeSpectrum.basicOpen t ≤ PrimeSpectrum.basicOpen r)
    (a : Localization.Away r →ₐ[S] Localization.Away t) :
    (basicOpenIsoSpecAway (R := .of S) t).inv ≫ (Spec (.of S)).homOfLE h ≫
      (basicOpenIsoSpecAway (R := .of S) r).hom = Spec.map (CommRingCat.ofHom a.toRingHom) := by
  rw [← cancel_mono (Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away r))))]
  rw [Category.assoc, Category.assoc, basicOpenIsoSpecAway_hom_SpecMap, Scheme.homOfLE_ι]
  have ha : a.toRingHom.comp (algebraMap S (Localization.Away r)) =
      algebraMap S (Localization.Away t) := by
    ext x
    exact a.commutes x
  rw [← Spec.map_comp]
  change (basicOpenIsoSpecAway (R := .of S) t).inv ≫ _ =
    Spec.map (CommRingCat.ofHom (a.toRingHom.comp (algebraMap S (Localization.Away r))))
  rw [ha, ← basicOpenIsoSpecAway_hom_SpecMap (R := .of S) t, Iso.inv_hom_id_assoc]

end FLT.Mazur.HilbertChart
