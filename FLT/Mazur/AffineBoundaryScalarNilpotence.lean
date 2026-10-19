/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarIdealNilpotenceResidual
public import FLT.Mazur.AffineBoundaryNilpotenceOpen

/-!
# Original scalar neighborhoods of the full boundary product

The second projection records the unchanged scalar prime. Its coordinate
homomorphism turns scalar-local ideal certificates into genuine scalar
neighborhoods; no arbitrary product denominator is treated as a scalar.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.AffineScalarBoundaryNilpotence
open ScalarLocalizedIdealNilpotence
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R B T : Type} [CommRing R] [CommRing B] [CommRing T]
  (s : R →+* B) (κ : R →+* T)

/-- The second projection retains the original scalar prime of a product point. -/
def boundaryScalarProjection : boundaryProduct s κ ⟶ Spec (.of T) :=
  pullback.snd _ _

/-- The actual original scalar ring acts through global functions on the unchanged product. -/
def boundaryScalarHom : T →+* Γ(boundaryProduct s κ, ⊤) :=
  (boundaryScalarProjection s κ).appTop.hom.comp (Scheme.ΓSpecIso (.of T)).inv.hom

attribute [local irreducible] boundaryProduct boundaryCoordinate
set_option quotPrecheck false
local notation "C" => Γ(boundaryProduct s κ, ⊤)

/-- Original scalar principal opens pull back to the corresponding product principal opens. -/
theorem boundaryScalarHom_basicOpen (t : T) :
    (boundaryProduct s κ).basicOpen (boundaryScalarHom s κ t) =
      boundaryScalarProjection s κ ⁻¹ᵁ PrimeSpectrum.basicOpen t := by
  change (boundaryProduct s κ).basicOpen
    ((boundaryScalarProjection s κ).appTop ((Scheme.ΓSpecIso (.of T)).inv t)) = _
  rw [← Scheme.preimage_basicOpen_top, basicOpen_eq_of_affine]

/-- Contraction of a coordinate prime is exactly the original scalar center. -/
theorem boundaryScalarHom_comap_point (z : boundaryProduct s κ) :
    (((boundaryProduct s κ).isoSpec.hom z).asIdeal).comap (boundaryScalarHom s κ) =
      (boundaryScalarProjection s κ z).asIdeal := by
  ext t
  apply not_iff_not.mp
  change z ∈ (boundaryProduct s κ).toSpecΓ ⁻¹ᵁ
    PrimeSpectrum.basicOpen (boundaryScalarHom s κ t) ↔ _
  rw [Scheme.toSpecΓ_preimage_basicOpen, boundaryScalarHom_basicOpen]
  rfl

/-- A minimal coefficient component keeps its actual scalar center under contraction. -/
theorem boundaryScalarHom_comap_component (Q : minimalPrimes C) :
    Q.val.comap (boundaryScalarHom s κ) =
      (boundaryScalarProjection s κ (boundaryComponentPoint s κ Q)).asIdeal := by
  have he : (boundaryProduct s κ).isoSpec.hom (boundaryComponentPoint s κ Q) =
      (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C) :=
    congrArg (fun f ↦ f (⟨Q.val, Q.property.1.1⟩ : PrimeSpectrum C))
      (boundaryProduct s κ).isoSpec.inv_hom_id
  simpa only [he] using boundaryScalarHom_comap_point s κ (boundaryComponentPoint s κ Q)

variable (a : Finset B)
local notation "I" => boundaryTestIdeal s κ a

/-- The largest original scalar open carrying full local nilpotence on the whole product. -/
def boundaryScalarNilpotenceOpen : TopologicalSpace.Opens (PrimeSpectrum T) :=
  scalarNilpotenceOpen (boundaryScalarHom s κ) I

/-- Membership supplies an actual scalar outside the specified prime and a full power equation. -/
theorem mem_boundaryScalarNilpotenceOpen (P : PrimeSpectrum T) :
    P ∈ boundaryScalarNilpotenceOpen s κ a ↔
      ∃ (k : ℕ) (t : T), t ∉ P.asIdeal ∧
        boundaryScalarHom s κ t ∈ (I ^ k).annihilator :=
  mem_scalarNilpotenceOpen (boundaryScalarHom s κ) I P

/-- Only minimal components whose unchanged scalar centers generize the prime are tested. -/
theorem mem_boundaryScalarNilpotenceOpen_iff_components (P : PrimeSpectrum T) :
    P ∈ boundaryScalarNilpotenceOpen s κ a ↔
      ∀ Q : minimalPrimes C,
        (boundaryScalarProjection s κ (boundaryComponentPoint s κ Q)).asIdeal ≤ P.asIdeal →
          I ≤ Q.val := by
  change P ∈ scalarNilpotenceOpen (boundaryScalarHom s κ) I ↔ _
  rw [mem_scalarNilpotenceOpen_iff_components _ _ (boundaryTestIdeal_fg s κ a)]
  simp_rw [boundaryScalarHom_comap_component]

/-- Every point above the scalar nilpotence open has full local product nilpotence. -/
theorem boundaryScalarNilpotenceOpen_preimage :
    boundaryScalarProjection s κ ⁻¹' (boundaryScalarNilpotenceOpen s κ a :
      Set (PrimeSpectrum T)) ⊆ boundaryNilpotenceOpen s κ a := by
  intro z hz
  obtain ⟨k, t, ht, ha⟩ := (mem_boundaryScalarNilpotenceOpen s κ a _).mp hz
  apply (mem_boundaryNilpotenceOpen s κ a z).mpr
  refine ⟨k, boundaryScalarHom s κ t, ?_, ha⟩
  change t ∉ (((boundaryProduct s κ).isoSpec.hom z).asIdeal).comap (boundaryScalarHom s κ)
  rwa [boundaryScalarHom_comap_point]

/-- Scalar coverage is still the unchanged full-product nilpotence equation. -/
theorem boundaryScalarNilpotenceOpen_eq_top_iff :
    boundaryScalarNilpotenceOpen s κ a = ⊤ ↔ IsNilpotent I :=
  scalarNilpotenceOpen_eq_top_iff (boundaryScalarHom s κ) I (boundaryTestIdeal_fg s κ a)

end FLT.Mazur.AffineScalarBoundaryNilpotence
