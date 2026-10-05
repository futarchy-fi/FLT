/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DivisorStalkLength
public import FLT.Mazur.FiniteSchemeLength
public import FLT.Mazur.IntegralClosedSupport

/-!
# Finite divisor length on reduced closed components

A finite closed subscheme remains finite after restriction to a closed component.
Its field length is positive exactly when that component meets the divisor
support. The definition uses the actual restricted ideal and structure morphism;
identification with the Euler-characteristic degree of O(D) is a separate step.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

open CoherentDevissage

variable {k : Type u} [Field k] {X Y : Scheme.{u}}
  (f : X ⟶ Spec (CommRingCat.of k)) (I : X.IdealSheafData)

/-- Field length of the actual closed subscheme defined by an ideal sheaf. -/
def divisorFieldLength : ℕ := finiteSchemeLength (I.subschemeι ≫ f)

/-- Field length detects nonempty divisor support. -/
theorem divisorFieldLength_pos_iff [IsFinite (I.subschemeι ≫ f)] :
    0 < divisorFieldLength f I ↔ (I.support : Set X).Nonempty := by
  rw [divisorFieldLength, finiteSchemeLength_pos_iff]
  constructor
  · rintro ⟨x⟩
    exact ⟨I.subschemeι x, (I.range_subschemeι ▸ Set.mem_range_self x)⟩
  · rintro ⟨x, hx⟩
    obtain ⟨y, _⟩ := (I.range_subschemeι ▸ hx : x ∈ Set.range I.subschemeι)
    exact ⟨y⟩

/-- Field length detects the existence of a positive quotient-stalk length. -/
theorem divisorFieldLength_pos_iff_exists_stalk [IsFinite (I.subschemeι ≫ f)] :
    0 < divisorFieldLength f I ↔ ∃ x : X, 0 < divisorStalkLength I x := by
  simp only [divisorFieldLength_pos_iff, divisorStalkLength_pos_iff, Set.Nonempty]
  rfl

/-- Restricting a finite divisor along a closed immersion remains finite over the field. -/
theorem divisor_comap_isFinite (i : Y ⟶ X) [IsClosedImmersion i]
    [IsFinite (I.subschemeι ≫ f)] :
    IsFinite ((I.comap i).subschemeι ≫ i ≫ f) := by
  have he : (I.comap i).subschemeι ≫ i ≫ f =
      (I.comapIso i).hom ≫ pullback.snd i I.subschemeι ≫ (I.subschemeι ≫ f) := by
    rw [← I.comapIso_hom_fst i, Category.assoc, pullback.condition_assoc]
  rw [he]
  infer_instance

/-- Restricted divisor length detects intersection with the closed image. -/
theorem divisorFieldLength_comap_pos_iff (i : Y ⟶ X) [IsClosedImmersion i]
    [IsFinite (I.subschemeι ≫ f)] :
    0 < divisorFieldLength (i ≫ f) (I.comap i) ↔
      ((I.support : Set X) ∩ Set.range i).Nonempty := by
  have := divisor_comap_isFinite f I i
  rw [divisorFieldLength_pos_iff, Scheme.IdealSheafData.support_comap]
  change (i ⁻¹' (I.support : Set X)).Nonempty ↔ _
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨i y, hy, y, rfl⟩
  · rintro ⟨x, hx, y, rfl⟩
    exact ⟨y, hx⟩

/-- The length of the actual divisor restricted to the reduced closed subscheme. -/
def reducedComponentDivisorLength (Z : Closeds X) : ℕ :=
  divisorFieldLength (reducedClosedSubschemeι Z ≫ f) (I.comap (reducedClosedSubschemeι Z))

/-- A reduced component has positive divisor length precisely when it meets support. -/
theorem reducedComponentDivisorLength_pos_iff (Z : Closeds X)
    [IsFinite (I.subschemeι ≫ f)] :
    0 < reducedComponentDivisorLength f I Z ↔
      ((I.support : Set X) ∩ Z).Nonempty := by
  rw [reducedComponentDivisorLength, divisorFieldLength_comap_pos_iff,
    range_reducedClosedSubschemeι]

/-- The pointwise support criterion for every actual irreducible component. -/
theorem component_divisor_length_pos_iff [IsFinite (I.subschemeι ≫ f)] :
    (∀ (Z : Set X) (hZ : Z ∈ irreducibleComponents X),
      0 < reducedComponentDivisorLength f I ⟨Z, isClosed_of_mem_irreducibleComponents Z hZ⟩) ↔
    ∀ Z ∈ irreducibleComponents X, ((I.support : Set X) ∩ Z).Nonempty := by
  simp only [reducedComponentDivisorLength_pos_iff]
  rfl

end FLT.Mazur.FCurve
