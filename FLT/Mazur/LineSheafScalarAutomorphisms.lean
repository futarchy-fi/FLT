/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.LineSheafGlobalEndomorphisms

/-!
# Automorphisms of a line sheaf

An actual scalar endomorphism is invertible exactly when its coefficient is a
unit. Thus every line-sheaf automorphism has a unique invertible global coefficient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.ModuleSheafScalarEndomorphisms
open IdealPowerScalarLift IdealAdicQuotient
variable {X : Scheme.{u}} {M : X.Modules}

/-- A unit acts by an actual module-sheaf automorphism. -/
def scalarUnitIso (M : X.Modules) (r : Γ(X, ⊤)ˣ) : M ≅ M where
  hom := scalarEnd M (r : Γ(X, ⊤))
  inv := scalarEnd M (↑r⁻¹ : Γ(X, ⊤))
  hom_inv_id := by rw [scalarEnd_mul, Units.inv_mul, scalarEnd_one]
  inv_hom_id := by rw [scalarEnd_mul, Units.mul_inv, scalarEnd_one]

/-- A scalar line-sheaf endomorphism is invertible precisely for a unit coefficient. -/
theorem scalarEnd_isIso_iff (hM : LocallyFreeRankOne M) (r : Γ(X, ⊤)) :
    IsIso (scalarEnd M r) ↔ IsUnit r := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (scalarEnd_bijective hM).surjective (inv (scalarEnd M r))
    apply isUnit_iff_exists_inv.mpr
    refine ⟨s, ?_⟩
    apply (scalarEnd_bijective hM).injective
    rw [← scalarEnd_mul, hs, IsIso.inv_hom_id, scalarEnd_one]
  · rintro ⟨r, rfl⟩
    exact inferInstanceAs (IsIso (scalarUnitIso M r).hom)

/-- Every actual line automorphism is multiplication by a unique unit. -/
theorem existsUnique_scalarUnit (hM : LocallyFreeRankOne M) (e : M ≅ M) :
    ∃! r : Γ(X, ⊤)ˣ, scalarUnitIso M r = e := by
  obtain ⟨r, hr⟩ := (scalarEnd_bijective hM).surjective e.hom
  have hi : IsIso (scalarEnd M r) := hr.symm ▸ inferInstance
  obtain ⟨r, rfl⟩ := (scalarEnd_isIso_iff hM r).mp hi
  refine ⟨r, Iso.ext hr, ?_⟩
  intro s hs
  apply Units.ext
  apply (scalarEnd_bijective hM).injective
  exact (congrArg Iso.hom hs).trans hr.symm

end FLT.Mazur.FCurve.ModuleSheafScalarEndomorphisms
