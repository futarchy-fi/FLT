/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PrincipalOpenTensorGeometry

/-!
# Full principal opens under an algebra normalization

An algebra equivalence identifies the whole localization at an original
function with the localization at its normalized image. The spectrum square
retains restriction of every function, without selecting a component.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.PrincipalOpenNormalization
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K A B : Type u} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra K B] (e : A ≃ₐ[K] B) (x : A)

/-- The entire original localization in normalized coordinates. -/
def equiv : Localization.Away x ≃ₐ[K] Localization.Away (e x) :=
  IsLocalization.algEquivOfAlgEquiv _ _
    (M := Submonoid.powers x) (T := Submonoid.powers (e x)) e
    (by rw [Submonoid.map_powers])

/-- All original functions have their exact normalized restriction. -/
@[simp] theorem equiv_base (a : A) :
    equiv e x (algebraMap A _ a) = algebraMap B _ (e a) :=
  IsLocalization.algEquivOfAlgEquiv_eq _ a

/-- The whole original principal open and the normalized principal open are isomorphic. -/
def specIso : Spec (.of (Localization.Away (e x))) ≅
    Spec (.of (Localization.Away x)) :=
  Scheme.Spec.mapIso (equiv e x).toRingEquiv.toCommRingCatIso.op

/-- The normalized principal inclusion commutes with the complete original restriction. -/
@[reassoc] theorem specIso_inclusion :
    (specIso e x).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A _)) =
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (e x)))) ≫
        (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom := by
  change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  exact RingHom.ext (equiv_base e x)

/-- The full normalized principal inclusion is an open immersion. -/
instance normalizedInclusion_isOpenImmersion : IsOpenImmersion
    (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (e x))))) :=
  IsOpenImmersion.of_isLocalization (e x)

/-- Any original chart map retains the complete boundary after normalization. -/
@[reassoc] theorem specIso_chart {X : Scheme} (f : Spec (.of A) ⟶ X) :
    (specIso e x).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap A _)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (e x)))) ≫
        (Scheme.Spec.mapIso e.toRingEquiv.toCommRingCatIso.op).hom ≫ f :=
  specIso_inclusion_assoc e x f

end FLT.Mazur.PrincipalOpenNormalization
