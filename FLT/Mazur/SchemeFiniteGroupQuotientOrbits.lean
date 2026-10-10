/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFiniteGroupQuotient

/-!
# Actual scheme-point orbits in affine quotients

The invariant-coordinate quotient identifies exactly the orbits of the original
scheme action. Stable open subsets consequently descend to open subsets.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.SchemeCoordinateAction
open scoped Pointwise

namespace FLT.Mazur.SchemeFiniteGroupQuotient

universe u
variable {G : Type u} [Group G] [Finite G] {X : Scheme.{u}} [IsAffine X]
variable (ρ : G →* Aut X)

/-- Fibers of the affine quotient are precisely orbits under the actual scheme action. -/
theorem quotientMap_eq_iff_orbit (x y : X) :
    quotientMap ρ x = quotientMap ρ y ↔ ∃ g : G, y = (ρ g).hom x := by
  let _ := coordinateAction ρ
  constructor
  · intro h
    obtain ⟨g, hg⟩ := (FiniteGroupQuotient.spectrum_eq_iff_orbit G Γ(X, ⊤)
      (X.toSpecΓ x) (X.toSpecΓ y)).mp h
    refine ⟨g, X.toSpecΓ.homeomorph.injective ?_⟩
    change X.toSpecΓ y = ((ρ g).hom ≫ X.toSpecΓ) x
    rw [toSpecΓ_equivariant]
    apply PrimeSpectrum.ext
    change (X.toSpecΓ y).asIdeal =
      (X.toSpecΓ x).asIdeal.comap (coordinateHom ρ g⁻¹)
    rw [hg, Ideal.pointwise_smul_eq_comap]
    rfl
  · rintro ⟨g, rfl⟩
    exact (congrArg (fun f : X ⟶ quotient ρ ↦ f x) (quotientMap_invariant ρ g)).symm

/-- The quotient topology agrees with the scheme topology on the invariant spectrum. -/
lemma quotientMap_isQuotientMap : Topology.IsQuotientMap (quotientMap ρ) :=
  (quotientMap ρ).isClosedMap.isQuotientMap
    (quotientMap ρ).continuous (quotientMap ρ).surjective

/-- Stable sets are saturated for the affine quotient. -/
lemma quotientMap_saturated (U : Set X)
    (hU : ∀ (g : G) (x : X), x ∈ U → (ρ g).hom x ∈ U) :
    quotientMap ρ ⁻¹' (quotientMap ρ '' U) = U := by
  apply Set.Subset.antisymm
  · rintro y ⟨x, hx, hxy⟩
    obtain ⟨g, rfl⟩ := (quotientMap_eq_iff_orbit ρ x y).mp hxy
    exact hU g x hx
  · exact Set.subset_preimage_image _ _

/-- A stable open in an affine chart has an open image in its quotient. -/
lemma quotientMap_image_isOpen (U : Set X) (ho : IsOpen U)
    (hU : ∀ (g : G) (x : X), x ∈ U → (ρ g).hom x ∈ U) :
    IsOpen (quotientMap ρ '' U) := by
  rw [← (quotientMap_isQuotientMap ρ).isOpen_preimage, quotientMap_saturated ρ U hU]
  exact ho

end FLT.Mazur.SchemeFiniteGroupQuotient
