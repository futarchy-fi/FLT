/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatGlobalSections
public import FLT.Mazur.SchemeFiniteTargetAffineNeighborhood

/-!
# The exact locus of whole-preimage finite-projective affine neighborhoods

For flat locally finitely presented morphisms, these neighborhoods exist
precisely on the original finite target locus. This does not replace the
whole original preimage with a selected finite part of a point fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} (p : D ⟶ A)

/-- A genuine affine whole preimage with finite-projective original sections. -/
def HasProjectivePreimage (U : A.affineOpens) : Prop :=
  IsAffine (p ⁻¹ᵁ U.1).toScheme ∧
    let _ := (p ∣_ U.1).appTop.hom.toAlgebra
    Module.Finite Γ(U.1, ⊤) Γ((p ⁻¹ᵁ U.1).toScheme, ⊤) ∧
      Module.Projective Γ(U.1, ⊤) Γ((p ⁻¹ᵁ U.1).toScheme, ⊤)

/-- Finite actual coordinate sections recover finiteness of the whole restricted morphism. -/
theorem finite_restrict_of_projectivePreimage (U : A.affineOpens)
    (h : HasProjectivePreimage p U) : IsFinite (p ∣_ U.1) := by
  let _ := h.1
  apply (HasAffineProperty.iff_of_isAffine (P := @IsFinite)).mpr
  exact ⟨inferInstance, h.2.1⟩

variable [Flat p] [LocallyOfFinitePresentation p]

/-- Geometry constructs finite projectivity on each finite affine target neighborhood. -/
theorem hasProjectivePreimage_of_finite (U : A.affineOpens) [IsFinite (p ∣_ U.1)] :
    HasProjectivePreimage p U := by
  let _ : IsAffine (p ⁻¹ᵁ U.1).toScheme := isAffine_of_isAffineHom (p ∣_ U.1)
  exact ⟨inferInstance, (p ∣_ U.1).finite_appTop,
    FCurve.finiteFlat_appTop_projective (p ∣_ U.1)⟩

/-- The precise finite-projective neighborhood locus is the original finite target locus. -/
theorem mem_finiteTargetOpen_iff_projectivePreimage (x : A) :
    x ∈ finiteTargetOpen p ↔
      ∃ U : A.affineOpens, x ∈ U.1 ∧ HasProjectivePreimage p U := by
  rw [mem_finiteTargetOpen_iff_affine]
  constructor
  · rintro ⟨U, hx, hU⟩
    let _ := hU
    exact ⟨U, hx, hasProjectivePreimage_of_finite p U⟩
  · rintro ⟨U, hx, hU⟩
    exact ⟨U, hx, finite_restrict_of_projectivePreimage p U hU⟩

/-- The actual finite-projective neighborhoods can be chosen inside a prescribed target open. -/
theorem exists_projectivePreimage_inside (x : A) (hx : x ∈ finiteTargetOpen p)
    (O : A.Opens) (hxO : x ∈ O) :
    ∃ U : A.affineOpens, x ∈ U.1 ∧ U.1 ≤ O ∧ HasProjectivePreimage p U := by
  obtain ⟨U, hxU, hUO, hU⟩ := exists_finite_affine_target p x hx O hxO
  let _ := hU
  exact ⟨U, hxU, hUO, hasProjectivePreimage_of_finite p U⟩

end FLT.Mazur.SchemeOpenEnvelope
