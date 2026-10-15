/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteEnvelopeInteriorEquations

/-!
# Radical transport of the original envelope boundary ideal

Equality of inverse images of the original interior gives equality of the
radicals of the pulled-back denominator ideals on every affine test scheme.
This is an ideal-theoretic descent identity, not equality of invariant
functions or of possibly nonreduced closed subschemes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
universe u
set_option backward.isDefEq.respectTransparency false

/-- On an affine scheme the zero set detects precisely the radical of a global ideal. -/
theorem affine_zeroLocus_eq_iff {Z : Scheme.{u}} [IsAffine Z]
    (I J : Ideal Γ(Z, ⊤)) :
    Z.zeroLocus (I : Set Γ(Z, ⊤)) = Z.zeroLocus (J : Set Γ(Z, ⊤)) ↔
      I.radical = J.radical := by
  constructor
  · intro h
    apply PrimeSpectrum.zeroLocus_eq_iff.mp
    rw [← Z.toSpecΓ_image_zeroLocus, ← Z.toSpecΓ_image_zeroLocus, h]
  · intro h
    rw [← Z.zeroLocus_radical I, ← Z.zeroLocus_radical J, h]

/-- A global ideal on an affine test has empty zero set exactly when it is the unit ideal. -/
theorem affine_zeroLocus_empty_iff {Z : Scheme.{u}} [IsAffine Z]
    (I : Ideal Γ(Z, ⊤)) : Z.zeroLocus (I : Set Γ(Z, ⊤)) = ∅ ↔ I = ⊤ := by
  constructor
  · intro h
    apply PrimeSpectrum.zeroLocus_empty_iff_eq_top.mp
    rw [← Z.toSpecΓ_image_zeroLocus, h, Set.image_empty]
  · intro h
    rw [← Z.toSpecΓ_preimage_zeroLocus,
      PrimeSpectrum.zeroLocus_empty_iff_eq_top.mpr h, Set.preimage_empty]

variable {Y X Z : Scheme.{u}} (π : Y ⟶ X) (O : Y.Opens) [IsAffine X]

/-- The boundary ideal pulls back to the complement of the pulled-back original interior. -/
theorem zeroLocus_map_denominator (a : Z ⟶ X) :
    Z.zeroLocus ((denominatorIdeal π.appTop.hom O).map a.appTop.hom : Set Γ(Z, ⊤)) =
      (a ⁻¹' (fullFiberInterior π O : Set X))ᶜ := by
  have hz : Z.zeroLocus (a.appTop.hom ''
      (denominatorIdeal π.appTop.hom O : Set Γ(X, ⊤))) =
      a ⁻¹' X.zeroLocus (denominatorIdeal π.appTop.hom O : Set Γ(X, ⊤)) := by
    ext z
    simp only [Scheme.mem_zeroLocus_iff, Set.forall_mem_image, Set.mem_preimage]
    exact forall_congr' fun r ↦ forall_congr' fun _ ↦ by
      rw [← Scheme.Hom.preimage_basicOpen_top]
      rfl
  rw [Ideal.map, Z.zeroLocus_span, hz, zeroLocus_denominatorIdeal]
  change a ⁻¹' closure (π '' (O : Set Y)ᶜ) =
    (a ⁻¹' interior (π '' (O : Set Y)ᶜ)ᶜ)ᶜ
  rw [interior_compl, Set.preimage_compl, compl_compl]

/-- Invariant original interiors have equal radical boundary ideals on affine scheme tests. -/
theorem radical_map_denominator_eq [IsAffine Z] (a b : Z ⟶ X)
    (h : a ⁻¹ᵁ fullFiberInterior π O = b ⁻¹ᵁ fullFiberInterior π O) :
    ((denominatorIdeal π.appTop.hom O).map a.appTop.hom).radical =
      ((denominatorIdeal π.appTop.hom O).map b.appTop.hom).radical := by
  apply (affine_zeroLocus_eq_iff _ _).mp
  rw [zeroLocus_map_denominator, zeroLocus_map_denominator]
  exact congrArg (fun U : Z.Opens ↦ (U : Set Z)ᶜ) h

end FLT.Mazur.SchemeOpenEnvelope
