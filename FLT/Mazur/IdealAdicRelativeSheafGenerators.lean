/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicRelativeSheafFinite
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-!
# A finite generating family for the actual relative coefficient sheaf

The actual quotient is an epimorphism of module sheaves: each section lifts
on an affine neighborhood. Its unit section is therefore a single global
generator in the sheaf sense. No surjectivity on arbitrary-open sections or
finite-presentation assertion is made.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsAffine Y]
variable (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- The original glued quotient as a morphism of actual relative module sheaves. -/
def relativeModuleQuotient : SheafOfModules.unit (relativeScalarSheaf J f) ⟶
    relativeCoefficientModuleSheaf J f :=
  ⟨{ app U := ModuleCat.ofHom
       (X := (SheafOfModules.unit (relativeScalarSheaf J f)).val.obj U)
       (Y := (relativeCoefficientModuleSheaf J f).val.obj U)
       (relativeSheafQuotientLinear J f U)
     naturality := by
       intro U V i
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro r
       exact ConcreteCategory.congr_hom ((relativeSheafQuotient J f).hom.naturality i) r }⟩

/-- Every section of the glued coefficient module lifts on an affine neighborhood. -/
instance relativeModuleQuotient_locallySurjective :
    Sheaf.IsLocallySurjective
      ((SheafOfModules.toSheaf (relativeScalarSheaf J f)).map (relativeModuleQuotient J f)) where
  imageSieve_mem {U} s := by
    intro x hx
    obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset hx
    refine ⟨V, homOfLE hVU, ?_, hxV⟩
    exact relativeSheafQuotient_surjective J f ⟨V, hV⟩
      ((relativeCoefficientModuleSheaf J f).val.presheaf.map (homOfLE hVU).op s)

/-- The actual relative coefficient sheaf is a quotient of the rank-one free sheaf. -/
instance relativeModuleQuotient_epi : Epi (relativeModuleQuotient J f) :=
  (SheafOfModules.toSheaf (relativeScalarSheaf J f)).epi_of_epi_map inferInstance

/-- The original quotient supplies one global generating section. -/
def relativeCoefficientGeneratingSections :
    (relativeCoefficientModuleSheaf J f).GeneratingSections where
  I := PUnit.{u + 1}
  s _ := (relativeCoefficientModuleSheaf J f).unitHomEquiv (relativeModuleQuotient J f)
  epi := by
    let M := relativeCoefficientModuleSheaf J f
    let q := M.freeHomEquiv.symm (fun _ : PUnit.{u + 1} ↦
      M.unitHomEquiv (relativeModuleQuotient J f))
    have h : SheafOfModules.ιFree PUnit.unit ≫ q = relativeModuleQuotient J f := by
      rw [← SheafOfModules.unitHomEquiv_symm_freeHomEquiv_apply]
      simp only [q, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
    let _ : Epi (SheafOfModules.ιFree PUnit.unit ≫ q) := by
      rw [h]
      infer_instance
    exact epi_of_epi (SheafOfModules.ιFree PUnit.unit) q

/-- The proved generating family has one member, hence is finite. -/
instance relativeCoefficientGeneratingSections_finite :
    (relativeCoefficientGeneratingSections J f).IsFiniteType where
  finite := inferInstanceAs (Finite PUnit.{u + 1})

/-- The generating section is the actual unit in every coefficient ring of sections. -/
lemma relativeCoefficientGeneratingSections_one (U : X.Opensᵒᵖ) :
    relativeCoefficientSectionEquiv J f U
      (((relativeCoefficientGeneratingSections J f).s PUnit.unit).val U) = 1 :=
  ((relativeSheafQuotient J f).hom.app U).hom.map_one

end FLT.Mazur.IdealAdicGradedPullback
