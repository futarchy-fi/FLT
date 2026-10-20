/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarResidueClosureGeometry
public import FLT.Mazur.SchemeScalarAvoidanceCover

/-!
# The exact scalar image detected by original residue characters

Finite type produces a geometric endpoint over the original residue closure
at every prime in the actual image. Conversely, such an endpoint proves actual
image membership. No closedness or surjectivity of the scalar map is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
open SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] {X : Scheme} [IsAffine X]
  (s : R →+* Γ(X, ⊤)) (P : PrimeSpectrum R)
local notation "K" => scalarResidueClosure P
attribute [local semireducible] scalarResidueClosure
local notation "t" => Spec.map (CommRingCat.ofHom (algebraMap R K))

omit [IsAffine X] in
/-- A geometric endpoint with the original scalar character lies over the original prime. -/
theorem scalar_residue_endpoint_center (b : Spec (.of K) ⟶ X)
    (hb : b ≫ scalarMorphism s = t) : scalarMorphism s (b default) = P := by
  have h := congrArg (fun g : Spec (.of K) ⟶ Spec (.of R) ↦ g default) hb
  exact h.trans (scalarResidueClosure_center P)

/-- Every actual scalar image prime has a point over its own original residue closure. -/
theorem exists_scalar_residue_endpoint (hs : s.FiniteType)
    (hP : P ∈ Set.range (scalarMorphism s)) :
    ∃ b : Spec (.of K) ⟶ X, b ≫ scalarMorphism s = t := by
  obtain ⟨x, hx⟩ := hP
  obtain ⟨w, hw, _⟩ := exists_scalar_character_in_open s P hs ⊤ x (by trivial) hx
  let w' : Γ(X, ⊤) →+* K := w
  refine ⟨sourceCharacterMap w', ?_⟩
  rw [sourceCharacterMap_scalar]
  exact congrArg (fun a : R →+* K ↦ Spec.map (CommRingCat.ofHom a)) hw

/-- Original residue characters detect precisely the actual finite type scalar image. -/
theorem scalar_image_iff_residue_endpoint (hs : s.FiniteType) :
    P ∈ Set.range (scalarMorphism s) ↔
      ∃ b : Spec (.of K) ⟶ X, b ≫ scalarMorphism s = t := by
  refine ⟨exists_scalar_residue_endpoint s P hs, ?_⟩
  rintro ⟨b, hb⟩
  exact ⟨b default, scalar_residue_endpoint_center s P b hb⟩

omit [IsAffine X] in
/-- Affine source neighborhoods suffice to construct endpoints on a nonaffine original domain. -/
theorem exists_scalar_residue_endpoint_of_affineCover
    (hs : ∀ i, ((X.affineCover.f i).appTop.hom.comp s).FiniteType)
    (hP : P ∈ Set.range (scalarMorphism s)) :
    ∃ b : Spec (.of K) ⟶ X, b ≫ scalarMorphism s = t := by
  obtain ⟨x, hx⟩ := hP
  obtain ⟨i, y, hy⟩ := X.affineCover.exists_eq x
  obtain ⟨b, hb⟩ := exists_scalar_residue_endpoint
    ((X.affineCover.f i).appTop.hom.comp s) P (hs i) ⟨y, by
      rw [scalarMorphism_comp]
      change scalarMorphism s (X.affineCover.f i y) = P
      rwa [hy]⟩
  refine ⟨b ≫ X.affineCover.f i, ?_⟩
  rw [Category.assoc, ← scalarMorphism_comp]
  exact hb

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
