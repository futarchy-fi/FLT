/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBoundaryComponentEquations
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Minimal component generizations in the unchanged scalar product

Every original point is a specialization of an actual minimal coordinate
prime. No Noetherian or reduced hypothesis on the product is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] boundaryProduct
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T)
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)

/-- Ideal containment gives specialization of the actual component point in the full product. -/
theorem boundaryComponentPoint_specializes (Q : minimalPrimes C) (z : boundaryProduct s κ)
    (hQ : Q.val ≤ ((boundaryProduct s κ).isoSpec.hom z).asIdeal) :
    boundaryComponentPoint s κ Q ⤳ z := by
  have h := (PrimeSpectrum.le_iff_specializes
    (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C) ((boundaryProduct s κ).isoSpec.hom z)).mp hQ
  have hi := h.map (boundaryProduct s κ).isoSpec.inv.continuous
  have he : (boundaryProduct s κ).isoSpec.inv ((boundaryProduct s κ).isoSpec.hom z) = z :=
    congrArg (fun f ↦ f z) (boundaryProduct s κ).isoSpec.hom_inv_id
  exact he ▸ hi

/-- A minimal component point has no distinct generization in the full product. -/
theorem boundaryComponentPoint_generalization_eq (Q : minimalPrimes C)
    (z : boundaryProduct s κ) (hz : z ⤳ boundaryComponentPoint s κ Q) :
    z = boundaryComponentPoint s κ Q := by
  apply (boundaryProduct s κ).isoSpec.hom.homeomorph.injective
  have he : (boundaryProduct s κ).isoSpec.hom (boundaryComponentPoint s κ Q) =
      (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C) :=
    congrArg (fun f ↦ f (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C))
      (boundaryProduct s κ).isoSpec.inv_hom_id
  change (boundaryProduct s κ).isoSpec.hom z =
    (boundaryProduct s κ).isoSpec.hom (boundaryComponentPoint s κ Q)
  rw [he]
  have h := hz.map (boundaryProduct s κ).isoSpec.hom.continuous
  rw [he, ← PrimeSpectrum.le_iff_specializes] at h
  apply PrimeSpectrum.ext
  have hmin : Minimal Ideal.IsPrime Q.val := (IsMinimalPrime.iff_minimal Q.val).mp Q.property
  exact hmin.eq_of_le ((boundaryProduct s κ).isoSpec.hom z).isPrime h

/-- The full local scheme at a minimal component maps constantly on points, retaining nilpotents. -/
theorem boundaryComponentPoint_fromSpecStalk (Q : minimalPrimes C)
    (z : Spec ((boundaryProduct s κ).presheaf.stalk (boundaryComponentPoint s κ Q))) :
    (boundaryProduct s κ).fromSpecStalk (boundaryComponentPoint s κ Q) z =
      boundaryComponentPoint s κ Q := by
  apply boundaryComponentPoint_generalization_eq s κ
  have h := Set.mem_range_self
    (f := (boundaryProduct s κ).fromSpecStalk (boundaryComponentPoint s κ Q)) z
  rw [Scheme.range_fromSpecStalk] at h
  exact h

/-- Every original prime lies on a minimal component, retaining its full original point. -/
theorem exists_boundaryComponentPoint_specializes (z : boundaryProduct s κ) :
    ∃ Q : minimalPrimes C, boundaryComponentPoint s κ Q ⤳ z := by
  obtain ⟨Q, hQ, hle⟩ := Ideal.exists_minimalPrimes_le
    (show (⊥ : Ideal C) ≤ ((boundaryProduct s κ).isoSpec.hom z).asIdeal from bot_le)
  exact ⟨⟨Q, hQ⟩, boundaryComponentPoint_specializes s κ ⟨Q, hQ⟩ z hle⟩

/-- An open contains an actual point only if it contains a minimal component above that point. -/
theorem boundary_open_witness_component (V : (boundaryProduct s κ).Opens)
    (z : boundaryProduct s κ) (hz : z ∈ V) :
    ∃ Q : minimalPrimes C, boundaryComponentPoint s κ Q ⤳ z ∧
      boundaryComponentPoint s κ Q ∈ V := by
  obtain ⟨Q, hQ⟩ := exists_boundaryComponentPoint_specializes s κ z
  exact ⟨Q, hQ, hQ.mem_open V.isOpen hz⟩

/-- Empty minimal-component intersection proves emptiness of the entire original open. -/
theorem boundary_open_eq_bot_iff_components (V : (boundaryProduct s κ).Opens) :
    V = ⊥ ↔ ∀ Q : minimalPrimes C, boundaryComponentPoint s κ Q ∉ V := by
  constructor
  · rintro rfl Q
    exact id
  · intro h
    apply bot_unique
    intro z hz
    obtain ⟨Q, _, hQ⟩ := boundary_open_witness_component s κ V z hz
    exact h Q hQ

end FLT.Mazur.AffineScalarBoundaryNilpotence
