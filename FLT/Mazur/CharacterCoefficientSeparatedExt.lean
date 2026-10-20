/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CharacterSchemeBaseChange
public import FLT.Mazur.AffineSeparatedFamilyExt
public import FLT.Mazur.SurjectiveDominantEpi

/-!
# Injective character coefficients detect separated morphisms

Equality of maps from the full character source to a separated target can be
checked after an injective coefficient extension. Neither flatness nor
surjectivity on spectra is required, including for nonreduced character sources.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.CharacterSchemeBaseChange

open CharacterAlgebraScalarExtension

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u

variable (A B G : Type u) [CommRing A] [CommRing B] [Algebra A B] [AddCommMonoid G]
  (hAB : Function.Injective (algebraMap A B))

include hAB

/-- An injective extension of coefficients retains every character-algebra element. -/
theorem coeff_injective : Function.Injective (coeff A B G) :=
  AddMonoidAlgebra.map_injective _ hAB

/-- Its character spectrum map is schematically dominant, even when not surjective. -/
theorem coefficientMap_schematic : IsSchemeTheoreticallyDominant
    (Spec.map (CommRingCat.ofHom (coeff A B G).toRingHom)) :=
  SurjectiveDominantEpi.spec_schematic _ (coeff_injective A B G hAB)

/-- The full character coefficient extension detects morphisms into every separated target. -/
theorem coefficientMap_separated_hom_ext {Y S : Scheme.{u}} (s : Y ⟶ S) [IsSeparated s]
    {f g : (model A G).left ⟶ Y} (hfg : f ≫ s = g ≫ s)
    (he : Spec.map (CommRingCat.ofHom (coeff A B G).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom (coeff A B G).toRingHom) ≫ g) : f = g := by
  let _ : IsAffine (model A G).left :=
    inferInstanceAs (IsAffine (Spec (.of (AddMonoidAlgebra A G))))
  let v := Spec.map (CommRingCat.ofHom (coeff A B G).toRingHom)
  let _ : IsSchemeTheoreticallyDominant v := coefficientMap_schematic A B G hAB
  apply AffineSeparatedFamilyExt.hom_ext s hfg (fun _ : Unit => (model B G).left)
    (fun _ => v) ?_ (fun _ => he)
  intro x hx
  have hv : Function.Injective v.appTop := v.app_injective ⊤
  apply hv
  exact (hx ()).trans (map_zero v.appTop.hom).symm

end FLT.Mazur.CharacterSchemeBaseChange
