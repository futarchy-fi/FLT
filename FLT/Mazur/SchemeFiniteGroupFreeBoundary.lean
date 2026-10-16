/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteGroupFreeFieldTest
public import FLT.Mazur.SchemeFiniteGroupQuotientMaps
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Closed boundaries of affine quotients by free finite actions

Freeness on field-valued scheme points constructs the fixed-point unit ideals.
An equivariant closed immersion then induces a surjection on the actual
invariant coordinates and a closed immersion of the constructed quotient
schemes. The finite boundary certificate is proved for every section.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction
namespace FLT.Mazur.SchemeFiniteGroupQuotient
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {G : Type u} [Group G] {Y : Scheme.{u}} [IsAffine Y] (τ : G →* Aut Y)
  (hfree : ∀ (K : Type u) [Field K] (a : Spec (.of K) ⟶ Y) (g : G),
    a ≫ (τ g).hom = a → g = 1)
include hfree

/-- Actual field-valued scheme freeness forces all nonidentity fixed-point ideals to be one. -/
theorem coordinate_fixedPointIdeal_eq_top (g : G) (hg : g ≠ 1) :
    let _ := coordinateAction τ
    FiniteGroupQuotient.fixedPointIdeal G Γ(Y, ⊤) g = ⊤ := by
  let _ := coordinateAction τ
  apply FiniteGroupQuotient.fixedPointIdeal_eq_top_of_field_tests G ?_ g hg
  intro K _ φ h hh
  let a : Spec (.of K) ⟶ Y :=
    Spec.map (CommRingCat.ofHom φ) ≫ (asIso Y.toSpecΓ).inv
  have ha : a ≫ Y.toSpecΓ = Spec.map (CommRingCat.ofHom φ) := by
    simp [a]
  have he : a ≫ (τ h⁻¹).hom = a := by
    apply (cancel_mono Y.toSpecΓ).mp
    rw [Category.assoc, toSpecΓ_equivariant, inv_inv, ← Category.assoc, ha,
      ← Spec.map_comp]
    apply congrArg Spec.map
    ext r
    exact hh r
  exact inv_eq_one.mp (hfree K a h⁻¹ he)

variable [Finite G] {X : Scheme.{u}} (ρ : G →* Aut X) (i : X ⟶ Y)
  [IsClosedImmersion i] (hi : ∀ g : G, (ρ g).hom ≫ i = i ≫ (τ g).hom)

/-- The original closed immersion lifts all invariant boundary coordinates. -/
theorem invariantMap_surjective_of_free : Function.Surjective (invariantMap ρ τ i hi) := by
  let _ := coordinateAction ρ
  let _ := coordinateAction τ
  have he : ∀ (g : G) a, i.appTop.hom (g • a) = g • i.appTop.hom a := by
    intro g a
    exact (congrArg (fun f : Γ(Y, ⊤) →+* Γ(X, ⊤) ↦ f a)
      (coordinateHom_comp ρ τ i hi g)).symm
  exact FiniteGroupQuotient.boundaryMap_surjective_of_free G i.appTop.hom he
    (IsClosedImmersion.isAffine_surjective_of_isAffine i).2
    (coordinate_fixedPointIdeal_eq_top τ hfree)

/-- The actual map between quotient schemes is a closed immersion. -/
theorem quotientHom_isClosedImmersion_of_free : IsClosedImmersion (quotientHom ρ τ i hi) :=
  IsClosedImmersion.spec_of_surjective _ (invariantMap_surjective_of_free τ hfree ρ i hi)

/-- Every original invariant boundary section has a finite source coefficient identity. -/
theorem invariant_boundary_certificate_of_free (t : invariantCoordinates ρ) :
    ∃ a : sectionLiftIdeal (invariantMap ρ τ i hi) t →₀ Γ(X, ⊤),
      a.sum (fun v b ↦ b * (invariantMap ρ τ i hi v.val).val) = 1 := by
  let _ := coordinateAction ρ
  apply (mem_sourceCertifiedSections_iff _ (FiniteGroupQuotient.inclusion G Γ(X, ⊤)) t).mp
  obtain ⟨a, rfl⟩ := invariantMap_surjective_of_free τ hfree ρ i hi t
  exact image_mem_sourceCertifiedSections _ _ a

end FLT.Mazur.SchemeFiniteGroupQuotient
