/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicRestrictedPrincipal

/-!
# Localization for the canonical principal restrictions

Transport invariant localization along the actual global and principal section
identifications. Their restriction equation supplies the algebra compatibility.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (W : Opens (Orbit n))
local notation "Y" => invariantOpenSpace n W

/-- The canonical principal restriction localizes at the corresponding invariant section. -/
theorem restrictedPrincipal_isLocalization
    (s : (invariantSheaf n).obj.obj (op W)) :
    let r : (Y).presheaf.obj (op ⊤) := (invariantOpenSectionsIso n W).inv s
    let _ := ((Y).toToΓSpecMapBasicOpen r).hom.toAlgebra
    IsLocalization.Away r ((Y).presheaf.obj (op ((Y).toΓSpecMapBasicOpen r))) := by
  let e : (Y).presheaf.obj (op ⊤) ≃+* (invariantSheaf n).obj.obj (op W) :=
    (invariantOpenSectionsIso n W).commRingCatIsoToRingEquiv
  let r : (Y).presheaf.obj (op ⊤) := e.symm s
  let _ := (principalRestriction n W s).toAlgebra
  let _ := principalRestriction_isLocalization n W s
  have h := IsLocalization.isLocalization_of_base_ringEquiv (.powers s)
    ((invariantSheaf n).obj.obj (op (invariantPrincipal n W s))) e.symm
  rw [Submonoid.map_powers] at h
  let _ := ((principalRestriction n W s).comp e.toRingHom).toAlgebra
  let _ := ((Y).toToΓSpecMapBasicOpen r).hom.toAlgebra
  let f : (Y).presheaf.obj (op ((Y).toΓSpecMapBasicOpen r)) ≃ₐ[(Y).presheaf.obj (op ⊤)]
      (invariantSheaf n).obj.obj (op (invariantPrincipal n W s)) :=
    { (restrictedPrincipalSectionsIso n W s).commRingCatIsoToRingEquiv with
      commutes' := fun a => congrArg (fun k => k a)
        (restrictedPrincipalSectionsIso_restriction n W s) }
  exact (IsLocalization.isLocalization_iff_of_algEquiv (.powers r) f).mpr h

/-- Every canonical principal restriction of an invariant orbit open is localization. -/
theorem invariantOpenSpace_principal_isLocalization
    (r : (Y).presheaf.obj (op ⊤)) :
    let _ := ((Y).toToΓSpecMapBasicOpen r).hom.toAlgebra
    IsLocalization.Away r ((Y).presheaf.obj (op ((Y).toΓSpecMapBasicOpen r))) := by
  obtain ⟨s, hs⟩ := (invariantOpenSectionsIso n W).commRingCatIsoToRingEquiv.symm.surjective r
  subst r
  exact restrictedPrincipal_isLocalization n W s

end FLT.Mazur.CyclicCharacteristicOrbit
