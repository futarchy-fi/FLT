/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocallyFreeDegreeAffine
/-!
# Affine quotients of actual finite flat closed families

On a full inverse image of an affine base open, the ideal quotient is
identified with sections of the actual closed family. Its structure map,
finiteness, flatness, and module presentation follow from that family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
set_option backward.isDefEq.respectTransparency false
universe u
namespace FLT.Mazur.FCurve
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (I : X.IdealSheafData)
variable (U : Y.affineOpens) (hV : IsAffineOpen (f ⁻¹ᵁ U.1))
/-- The actual quotient structure map agrees with the closed-family section map. -/
theorem subscheme_quotient_structureMap :
    let _ := (f.app U).hom.toAlgebra
    (I.subschemeObjIso ⟨f ⁻¹ᵁ U.1, hV⟩).hom.hom.comp ((I.subschemeι ≫ f).app U).hom =
      algebraMap Γ(Y, U) (Γ(X, f ⁻¹ᵁ U.1) ⧸ I.ideal ⟨f ⁻¹ᵁ U.1, hV⟩) := by
  let _ := (f.app U).hom.toAlgebra
  change (((I.subschemeι ≫ f).app U) ≫
    (I.subschemeObjIso ⟨f ⁻¹ᵁ U.1, hV⟩).hom).hom = _
  rw [Scheme.Hom.comp_app, I.subschemeι_app ⟨f ⁻¹ᵁ U.1, hV⟩,
    Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  rfl
/-- Flatness of the closed family gives flatness of its actual affine quotient. -/
theorem flat_subscheme_ideal_quotient [Flat (I.subschemeι ≫ f)] :
    let _ := (f.app U).hom.toAlgebra
    Module.Flat Γ(Y, U) (Γ(X, f ⁻¹ᵁ U.1) ⧸ I.ideal ⟨f ⁻¹ᵁ U.1, hV⟩) := by
  let _ := (f.app U).hom.toAlgebra
  rw [← RingHom.flat_algebraMap_iff, ← subscheme_quotient_structureMap f I U hV]
  apply RingHom.Flat.comp ?_ (.of_bijective
    (I.subschemeObjIso ⟨f ⁻¹ᵁ U.1, hV⟩).commRingCatIsoToRingEquiv.bijective)
  simpa [Scheme.Hom.appLE] using
    (I.subschemeι ≫ f).flat_appLE U.2 (hV.preimage I.subschemeι) le_rfl

/-- Finiteness of the closed family gives a finite actual affine quotient. -/
theorem finite_subscheme_ideal_quotient [IsFinite (I.subschemeι ≫ f)] :
    let _ := (f.app U).hom.toAlgebra
    Module.Finite Γ(Y, U) (Γ(X, f ⁻¹ᵁ U.1) ⧸ I.ideal ⟨f ⁻¹ᵁ U.1, hV⟩) := by
  let _ := (f.app U).hom.toAlgebra
  rw [← RingHom.finite_algebraMap, ← subscheme_quotient_structureMap f I U hV]
  exact (RingHom.Finite.of_surjective _
    (I.subschemeObjIso ⟨f ⁻¹ᵁ U.1, hV⟩).commRingCatIsoToRingEquiv.surjective).comp
      ((I.subschemeι ≫ f).finite_app U U.2)

/-- A finite presented closed family has a finitely presented affine quotient module. -/
theorem finitePresentation_subscheme_ideal_quotient
    [IsFinite (I.subschemeι ≫ f)] [LocallyOfFinitePresentation (I.subschemeι ≫ f)] :
    let _ := (f.app U).hom.toAlgebra
    Module.FinitePresentation Γ(Y, U)
      (Γ(X, f ⁻¹ᵁ U.1) ⧸ I.ideal ⟨f ⁻¹ᵁ U.1, hV⟩) := by
  let _ := (f.app U).hom.toAlgebra
  let _ := finite_subscheme_ideal_quotient f I U hV
  have hp : (algebraMap Γ(Y, U)
      (Γ(X, f ⁻¹ᵁ U.1) ⧸ I.ideal ⟨f ⁻¹ᵁ U.1, hV⟩)).FinitePresentation := by
    rw [← subscheme_quotient_structureMap f I U hV]
    apply RingHom.FinitePresentation.comp
      (.of_surjective _ (I.subschemeObjIso ⟨f ⁻¹ᵁ U.1, hV⟩).commRingCatIsoToRingEquiv.surjective
        (by
          change (RingHom.ker
            (I.subschemeObjIso ⟨f ⁻¹ᵁ U.1, hV⟩).commRingCatIsoToRingEquiv.toRingHom).FG
          rw [RingEquiv.toRingHom_eq_coe, RingHom.ker_coe_equiv]
          exact Submodule.fg_bot))
    simpa [Scheme.Hom.appLE] using
      (I.subschemeι ≫ f).finitePresentation_appLE U.2 (hV.preimage I.subschemeι) le_rfl
  let _ := RingHom.finitePresentation_algebraMap.mp hp
  exact Module.FinitePresentation.of_finite_of_finitePresentation _ _

end FLT.Mazur.FCurve
