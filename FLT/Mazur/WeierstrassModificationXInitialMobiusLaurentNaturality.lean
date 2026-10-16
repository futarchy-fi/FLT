/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXInitialMobiusLaurentCoefficient

/-!
# Full scheme coefficient squares for the retained Laurent isomorphism

The actual forward and inverse reparametrizations both respect coefficient
restriction. The smoothing parameters may be constructed separately at each order.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open scoped LaurentPolynomial
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (ha : IsUnit W.a₁) (s τ : R)
  (hτ : s = W.a₁ ^ 2 * τ) (τ' : S) (hτ' : f s = (W.map f).a₁ ^ 2 * τ') (ht : f τ = τ')
  (b3 b4 b6 : R) (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)
  (hI : IsNilpotent I) (hJ : IsNilpotent J) (hs : s ∈ I)
  (h2 : W.a₂ ∈ I) (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "F" => PolygonScalingNaturality.coeffMap f
local notation "E" => initialMobiusLaurentIso W ha s τ hτ b3 b4 b6 I hI hs h2 h3 h4 h6
local notation "E'" => initialMobiusLaurentIso (W.map f) (ha.map f) (f s) τ' hτ'
  (f b3) (f b4) (f b6) J hJ (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)

include ht in
/-- The full arithmetic retained Laurent isomorphism commutes with coefficient restriction. -/
@[reassoc] theorem initialMobiusLaurentIso_coefficient :
    Spec.map (CommRingCat.ofHom F) ≫ (E).hom =
      (E').hom ≫ Spec.map (CommRingCat.ofHom F) := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact initialMobiusLaurentEquiv_coefficient f W ha s τ hτ τ' hτ' ht
    b3 b4 b6 I J hf hI hJ hs h2 h3 h4 h6

include ht in
/-- Inverse boundary reparametrizations give the same full arithmetic coefficient square. -/
@[reassoc] theorem initialMobiusLaurentIso_inv_coefficient :
    Spec.map (CommRingCat.ofHom F) ≫ (E).inv =
      (E').inv ≫ Spec.map (CommRingCat.ofHom F) := by
  apply (cancel_mono (E).hom).mp
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rw [initialMobiusLaurentIso_coefficient f W ha s τ hτ τ' hτ' ht
    b3 b4 b6 I J hf hI hJ hs h2 h3 h4 h6, Iso.inv_hom_id_assoc]

end FLT.Mazur.WeierstrassModificationX
