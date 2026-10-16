/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFactorRatioLaurentCoefficient

/-!
# Scheme coefficient squares for the corrected Laurent isomorphism

Both directions preserve the original Laurent coefficient maps and the
full squared-factor correction on every function.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s : R)
  (b3 b4 b6 : R) (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "F" => PolygonScalingNaturality.coeffMap f
local notation "u" => factorRatioLaurentUnit W ha s b3 b4 b6 I hI hs h2 h3 h4 h6
local notation "u'" => factorRatioLaurentUnit (W.map f) (ha.map f) (f s)
  (f b3) (f b4) (f b6) J hJ (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)
local notation "e" => factorRatioLaurentEquiv W ha s b3 b4 b6 I hI hs h2 h3 h4 h6
local notation "e'" => factorRatioLaurentEquiv (W.map f) (ha.map f) (f s)
  (f b3) (f b4) (f b6) J hJ (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)

local notation "E" => factorRatioLaurentIso W ha s b3 b4 b6 I hI hs h2 h3 h4 h6
local notation "E'" => factorRatioLaurentIso (W.map f) (ha.map f) (f s)
  (f b3) (f b4) (f b6) J hJ (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)
local notation "g" => Spec.map (CommRingCat.ofHom F)

/-- The exact full Laurent isomorphism follows the original coefficient morphism. -/
@[reassoc] theorem factorRatioLaurentIso_coefficient :
    g ≫ (E).hom = (E').hom ≫ g := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  simp only [← Spec.map_comp]
  exact congrArg (fun k ↦ Spec.map (CommRingCat.ofHom k))
    (factorRatioLaurentEquiv_coefficient f W ha s b3 b4 b6 I J hf hI hJ hs h2 h3 h4 h6)

/-- The whole inverse corrected Laurent parametrization preserves original coefficients. -/
@[reassoc] theorem factorRatioLaurentIso_inv_coefficient :
    g ≫ (E).inv = (E').inv ≫ g := by
  apply (cancel_mono (E).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [factorRatioLaurentIso_coefficient f W ha s b3 b4 b6 I J hf hI hJ hs h2 h3 h4 h6,
    Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassModificationX
