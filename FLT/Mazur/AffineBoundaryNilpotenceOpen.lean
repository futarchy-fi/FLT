/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIdealNilpotenceInterior
public import FLT.Mazur.AffineBoundaryGenericLocalTests

/-!
# Actual open nilpotence neighborhoods in the original scalar product

The open locus is built from original power-annihilating denominators. It is
the interior of the finite test neighborhood's support. Its complement retains
all specializations of failed tests, not only the points with a failed test.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open FiniteIdealLocalizationDenominators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct boundaryCoordinate
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T) (a : Finset B)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)
local notation "I" => boundaryTestIdeal s κ a

/-- The maximal open with nilpotent test ideal in every full original local ring. -/
def boundaryNilpotenceOpen : (boundaryProduct s κ).Opens :=
  (boundaryProduct s κ).isoSpec.hom ⁻¹ᵁ nilpotenceOpen I

/-- Each member supplies a denominator in the original coefficient ring and a power order. -/
theorem mem_boundaryNilpotenceOpen (z : boundaryProduct s κ) :
    z ∈ boundaryNilpotenceOpen s κ a ↔ ∃ k : ℕ, ∃ u : C,
      u ∉ ((boundaryProduct s κ).isoSpec.hom z).asIdeal ∧ u ∈ (I ^ k).annihilator :=
  mem_nilpotenceOpen I _

/-- Original coordinate-prime containment is exactly simultaneous vanishing of the tests. -/
theorem boundaryTestIdeal_le_point_iff (z : boundaryProduct s κ) :
    I ≤ ((boundaryProduct s κ).isoSpec.hom z).asIdeal ↔
      ∀ t ∈ a, t ∈ (boundaryProjection s κ z).asIdeal := by
  have he (t : B) : boundaryCoordinate s κ t ∈
      ((boundaryProduct s κ).isoSpec.hom z).asIdeal ↔
      t ∈ (boundaryProjection s κ z).asIdeal := by
    apply not_iff_not.mp
    change z ∈ (boundaryProduct s κ).toSpecΓ ⁻¹ᵁ
      PrimeSpectrum.basicOpen (boundaryCoordinate s κ t) ↔ _
    rw [Scheme.toSpecΓ_preimage_basicOpen, boundaryCoordinate_basicOpen]
    rfl
  rw [boundaryTestIdeal, Ideal.span_le]
  exact ⟨fun h t ht ↦ (he t).mp (h ⟨t, ht, rfl⟩),
    fun h _ ⟨t, ht, heq⟩ ↦ heq ▸ (he t).mpr (h t ht)⟩

/-- Pulling back the coordinate zero locus retains exactly each finite test stage's support. -/
theorem boundary_zeroLocus_preimage (k : ℕ) :
    (boundaryProduct s κ).isoSpec.hom ⁻¹' PrimeSpectrum.zeroLocus (I : Set C) =
      Set.range (boundaryTestThickeningMap s κ a k) := by
  ext z
  rw [Set.mem_preimage, PrimeSpectrum.mem_zeroLocus,
    mem_boundaryTestThickening_range]
  exact boundaryTestIdeal_le_point_iff s κ a z

/-- The open locus is exactly the interior of the actual finite test stage's support. -/
theorem boundaryNilpotenceOpen_eq_interior (k : ℕ) :
    (boundaryNilpotenceOpen s κ a : Set (boundaryProduct s κ)) =
      interior (Set.range (boundaryTestThickeningMap s κ a k)) := by
  change (boundaryProduct s κ).isoSpec.hom ⁻¹' (nilpotenceOpen I : Set (PrimeSpectrum C)) = _
  rw [nilpotenceOpen_eq_interior I (boundaryTestIdeal_fg s κ a)]
  change (boundaryProduct s κ).isoSpec.hom.homeomorph ⁻¹' interior _ = _
  rw [Homeomorph.preimage_interior]
  change interior ((boundaryProduct s κ).isoSpec.hom ⁻¹' _) = _
  rw [boundary_zeroLocus_preimage s κ a k]

/-- The remaining closed set includes every specialization of every failed original test. -/
theorem boundaryNilpotenceOpen_compl (k : ℕ) :
    (boundaryNilpotenceOpen s κ a : Set (boundaryProduct s κ))ᶜ =
      closure (Set.range (boundaryTestThickeningMap s κ a k))ᶜ := by
  rw [boundaryNilpotenceOpen_eq_interior s κ a k, closure_compl]

/-- A minimal component is in the actual open precisely when its full local ideal is nilpotent. -/
theorem boundaryComponent_mem_nilpotenceOpen (Q : minimalPrimes C) :
    boundaryComponentPoint s κ Q ∈ boundaryNilpotenceOpen s κ a ↔
      IsNilpotent (boundaryGenericTestIdeal s κ a Q) := by
  have he : (boundaryProduct s κ).isoSpec.hom (boundaryComponentPoint s κ Q) =
      (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C) :=
    congrArg (fun f ↦ f (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C))
      (boundaryProduct s κ).isoSpec.inv_hom_id
  change (boundaryProduct s κ).isoSpec.hom (boundaryComponentPoint s κ Q) ∈
    nilpotenceOpen I ↔ _
  rw [he, mem_nilpotenceOpen_iff_localized I (boundaryTestIdeal_fg s κ a)]
  rfl

/-- The entire original product is covered exactly when its actual finite ideal is nilpotent. -/
theorem boundaryNilpotenceOpen_eq_top_iff :
    boundaryNilpotenceOpen s κ a = ⊤ ↔ IsNilpotent I := by
  rw [← nilpotenceOpen_eq_top_iff I (boundaryTestIdeal_fg s κ a)]
  constructor
  · intro h
    apply top_unique
    intro P _
    obtain ⟨z, rfl⟩ := (boundaryProduct s κ).isoSpec.hom.surjective P
    have hz : z ∈ boundaryNilpotenceOpen s κ a := by rw [h]; trivial
    exact hz
  · intro h
    unfold boundaryNilpotenceOpen
    rw [h]
    rfl

end FLT.Mazur.AffineScalarBoundaryNilpotence
