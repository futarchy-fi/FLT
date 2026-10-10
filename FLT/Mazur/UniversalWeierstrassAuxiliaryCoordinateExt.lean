/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliaryCoordinateSections

/-!
# Actual auxiliary morphisms are determined by coefficients and labeled coordinates

Extensionality uses the original faithful representation. It does not assume
that the auxiliary scheme is affine or that its points determine its schemes.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.UniversalWeierstrass

open WeierstrassIntegralChart

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {T : Scheme} (f g : T ⟶ levelFour.left)

/-- Actual auxiliary maps are determined by their coefficient map and all marked sections. -/
theorem auxiliarySchemePoint_ext
    (hb : f ≫ levelFour.hom = g ≫ levelFour.hom)
    (hm : ∀ a, f ≫ (auxiliaryMarking 4 a).left = g ≫ (auxiliaryMarking 4 a).left) :
    f = g := by
  let p : Over.mk (f ≫ levelFour.hom) ⟶ levelFour := Over.homMk f rfl
  let q : Over.mk (f ≫ levelFour.hom) ⟶ levelFour := Over.homMk g hb.symm
  have he : p = q := by
    apply (AuxiliaryLevel.faithfulRepresentation universalGroup (Labels 4) _).injective
    apply Subtype.ext
    apply AuxiliaryLevel.homScheme_ext
    intro a
    apply Over.OverMorphism.ext
    exact (Category.assoc _ _ _).trans ((hm a).trans (Category.assoc _ _ _).symm)
  exact congrArg Over.Hom.left he

/-- Coefficients and the nonidentity affine sections suffice to identify an actual family. -/
theorem auxiliarySchemePoint_ext_affine
    (hb : f ≫ levelFour.hom = g ≫ levelFour.hom)
    (hm : ∀ (a : Labels 4) (ha : a ≠ 1),
      f ≫ auxiliaryAffineSection a ha = g ≫ auxiliaryAffineSection a ha) : f = g := by
  apply auxiliarySchemePoint_ext f g hb
  intro a
  by_cases ha : a = 1
  · subst a
    rw [map_one]
    change f ≫ (levelFour.hom ≫ _) = g ≫ (levelFour.hom ≫ _)
    rw [← Category.assoc, ← Category.assoc, hb]
  · rw [← auxiliaryAffineSection_inclusion a ha, ← Category.assoc, ← Category.assoc, hm a ha]

/-- Every original labeled coordinate and the coefficient map determine the entire morphism. -/
theorem auxiliarySchemePoint_ext_coordinates
    (hb : f ≫ levelFour.hom = g ≫ levelFour.hom)
    (hc : ∀ (a : Labels 4) (ha : a ≠ 1) (i : Fin 3),
      f.appTop.hom (auxiliaryCoordinate a ha i) =
        g.appTop.hom (auxiliaryCoordinate a ha i)) : f = g := by
  apply auxiliarySchemePoint_ext_affine f g hb
  intro a ha
  have hb' : f.appTop.hom.comp auxiliaryCoefficientSections =
      g.appTop.hom.comp auxiliaryCoefficientSections := by
    have h := congrArg (fun k => k.appTop.hom.comp
      (Scheme.ΓSpecIso (.of ParameterRing)).inv.hom) hb
    exact h
  let _ : Algebra ParameterRing Γ(T, ⊤) :=
    (f.appTop.hom.comp auxiliaryCoefficientSections).toAlgebra
  let u : Coordinate smoothEquation 2 →ₐ[ParameterRing] Γ(T, ⊤) :=
    { toRingHom := f.appTop.hom.comp (auxiliaryCoordinateSections a ha)
      commutes' := fun r => congrArg f.appTop.hom (auxiliaryCoordinateSections_coeff a ha r) }
  let v : Coordinate smoothEquation 2 →ₐ[ParameterRing] Γ(T, ⊤) :=
    { toRingHom := g.appTop.hom.comp (auxiliaryCoordinateSections a ha)
      commutes' := fun r =>
        (congrArg g.appTop.hom (auxiliaryCoordinateSections_coeff a ha r)).trans
          (DFunLike.congr_fun hb' r).symm }
  have huv : u = v := hom_ext smoothEquation 2 u v (hc a ha)
  apply ext_to_Spec
  apply CommRingCat.hom_ext
  exact congrArg AlgHom.toRingHom huv

end FLT.Mazur.UniversalWeierstrass
