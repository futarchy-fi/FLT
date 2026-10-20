/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicLocallyNormalizedModuli

/-!
# Sheaf-valued descent from original locally normalized modular classes

The actual local image of modular classes has the same maps to fppf sheaves
as the normalized unmarked parameter sheaf. This uses local extension and
the injective pointwise quotient, without assuming that the moduli presheaf
itself is a sheaf.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {F : Sheaf Scheme.fppfTopology (Type 1)}

/-- The actual pointwise unmarked classes include in the local modular image. -/
def unmarkedClassToLocalModuli :
    unmarkedParameterClassPresheaf n ⟶ (locallyNormalizedModuli n).toFunctor :=
  Subfunctor.toRange (unmarkedParameterModuliMap n) ≫
    Subfunctor.homOfLe ((normalizedModuliImage n).le_sheafify Scheme.fppfTopology)

/-- This inclusion recovers the original quotient sheaf map. -/
@[reassoc] theorem unmarkedClassToLocalModuli_map :
    unmarkedClassToLocalModuli n ≫ locallyNormalizedModuliMap n =
      unmarkedClassToSheaf n :=
  locallyNormalizedModuliMap_class n

/-- Maps from original locally normalized classes extend to the actual quotient sheaf. -/
def localModuliSheafDesc (t : (locallyNormalizedModuli n).toFunctor ⟶ F.obj) :
    unmarkedParameterSheaf n ⟶ F :=
  ⟨sheafifyLift Scheme.fppfTopology (unmarkedClassToLocalModuli n ≫ t) F.property⟩

/-- The extension retains the original pointwise modular classes. -/
@[reassoc] theorem localModuliSheafDesc_classes
    (t : (locallyNormalizedModuli n).toFunctor ⟶ F.obj) :
    unmarkedClassToSheaf n ≫ (localModuliSheafDesc n t).hom =
      unmarkedClassToLocalModuli n ≫ t :=
  toSheafify_sheafifyLift _ _ _

/-- Actual pointwise classes detect maps from the local image to any fppf sheaf. -/
theorem localModuli_hom_ext
    {a b : (locallyNormalizedModuli n).toFunctor ⟶ F.obj}
    (h : unmarkedClassToLocalModuli n ≫ a = unmarkedClassToLocalModuli n ≫ b) :
    a = b := by
  apply (normalizedModuliImage n).to_sheafify_lift_unique
    ((isSheaf_iff_isSheaf_of_type _ _).mp F.property)
  exact (cancel_epi (Subfunctor.toRange (unmarkedParameterModuliMap n))).mp h

/-- Extending to the quotient sheaf agrees on every original locally normalized class. -/
theorem localModuliSheafDesc_fac
    (t : (locallyNormalizedModuli n).toFunctor ⟶ F.obj) :
    locallyNormalizedModuliMap n ≫ (localModuliSheafDesc n t).hom = t := by
  apply localModuli_hom_ext n (F := F)
  rw [← Category.assoc, unmarkedClassToLocalModuli_map, localModuliSheafDesc_classes]

/-- The original local modular image detects maps out of the quotient sheaf. -/
theorem localModuliSheaf_hom_ext {a b : unmarkedParameterSheaf n ⟶ F}
    (h : locallyNormalizedModuliMap n ≫ a.hom =
      locallyNormalizedModuliMap n ≫ b.hom) : a = b := by
  apply Sheaf.hom_ext
  apply sheafify_hom_ext Scheme.fppfTopology _ _ F.property
  have he := congrArg (unmarkedClassToLocalModuli n ≫ ·) h
  simpa only [← Category.assoc, unmarkedClassToLocalModuli_map, unmarkedClassToSheaf] using he

/-- Sheaf extension of a map on original locally normalized classes is unique. -/
theorem localModuliSheafDesc_unique
    (t : (locallyNormalizedModuli n).toFunctor ⟶ F.obj)
    (d : unmarkedParameterSheaf n ⟶ F)
    (hd : locallyNormalizedModuliMap n ≫ d.hom = t) : d = localModuliSheafDesc n t :=
  localModuliSheaf_hom_ext n (hd.trans (localModuliSheafDesc_fac n t).symm)

end FLT.Mazur.CyclicCharacteristicAtlas
