/-
Copyright (c) 2026 FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FLT Project
-/
module

public import FLT.GaloisRepresentation.HardlyRamified.KummerModThreeCyclotomic
public import FLT.RepresentationTheory.ThreeGroupCharacters

/-!
# Conditional classification of simple category-D point characters

Assuming the named discriminant estimate, the actual augmented quotient
forces the point group to have dimension one over `ZMod 3`. Its character is
trivial or the mod-three cyclotomic character. This is a classification of
generic points; no identification of integral finite-flat models is asserted.
-/

@[expose] public noncomputable section

namespace ThreeAdicPlan

local notation "Γ" => AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ

/-- A simple category-D object's generic character is trivial or mod-three
cyclotomic, conditional only on the explicit discriminant estimate. -/
theorem Simple.point_character_of_discriminantBound
    {H : FiniteFlatObject ZInvTwo} (hs : Simple H) (hD : InCategoryD H)
    (hdisc : AugmentedDiscriminantBound H) :
    letI := hs.threeModule hD
    Module.finrank (ZMod 3) H.points = 1 ∧
      ∃ χ : Γ →* (ZMod 3)ˣ, (χ = 1 ∨ χ = modThreeCyclotomic) ∧
        ∀ (σ : Γ) (w : H.points), σ • w = (χ σ : ZMod 3) • w := by
  let := hs.threeModule hD
  let ρ := augmentedPointRepresentation H
  let φ := QuotientGroup.mk' (augmentedObject H).points.pointActionKernel
  let : Representation.IsIrreducible ρ :=
    hs.isIrreducible_of_pointAction ρ φ (augmentedPointRepresentation_apply H)
  obtain ⟨P, hnormal, hP, hcard⟩ :=
    augmentedPointGaloisGroup_normal_threeSubgroup hs hD hdisc
  let : P.Normal := hnormal
  obtain ⟨hdim, χ, _, hχ⟩ := ρ.simple_three_of_normal_threeSubgroup P hP (hcard ▸ dvd_rfl)
  refine ⟨hdim, χ.comp φ, ?_, ?_⟩
  · rcases Representation.character_eq_one_or_eq_of_normal_threeSubgroup P hP hcard
      (augmentedModThreeCyclotomic H) χ (augmentedModThreeCyclotomic_ne_one H) with h | h
    · left
      rw [h]
      rfl
    · right
      rw [h]
      rfl
  · intro σ w
    exact (augmentedPointRepresentation_apply H σ w).symm.trans (hχ (φ σ) w)

end ThreeAdicPlan
