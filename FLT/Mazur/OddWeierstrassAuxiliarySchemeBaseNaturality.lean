/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassAuxiliarySchemeRelativePoint

/-!
# Actual scheme normalization commutes with every source morphism

Coefficient naturality identifies the actual normalized bases over every
source scheme, before comparing the full auxiliary points.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.OddWeierstrassParameter

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {T U : Scheme} (f : T ⟶ levelThree.left) (k : U ⟶ T)

/-- The normalized coefficient parameter commutes with every change of source scheme. -/
theorem auxiliarySchemeNormalizedPoint_natural_base :
    auxiliarySchemeNormalizedPoint (k ≫ f) ≫ levelThree.hom =
      (k ≫ auxiliarySchemeNormalizedPoint f) ≫ levelThree.hom := by
  rw [Category.assoc, auxiliarySchemeNormalizedPoint_base,
    auxiliarySchemeNormalizedPoint_base, ← Category.assoc,
    Scheme.toSpecΓ_naturality, Category.assoc]
  apply congrArg (fun t => U.toSpecΓ ≫ t)
  change Spec.map (CommRingCat.ofHom
      (auxiliaryNormalizedCoefficientHom (k.appTop.hom.comp f.appTop.hom))) =
    Spec.map k.appTop ≫ Spec.map (CommRingCat.ofHom
      (auxiliaryNormalizedCoefficientHom f.appTop.hom))
  rw [← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  exact (auxiliaryNormalizedCoefficientHom_natural f.appTop.hom k.appTop.hom).symm

end FLT.Mazur.OddWeierstrassParameter
