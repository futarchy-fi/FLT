/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Basic

/-!
# Detecting full ideal membership on affine neighborhoods

A section belongs to an ideal if it does on an affine neighborhood of every
point. This retains the full ideal, including embedded and nilpotent parts.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffineIdealNeighborhoodMembership
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme} [IsAffine X] (I : Ideal Γ(X, ⊤)) (z : Γ(X, ⊤))

/-- Local membership on arbitrary affine neighborhoods detects the original global ideal. -/
theorem mem_of_neighborhoods
    (hl : ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op z ∈
        I.map (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom) : z ∈ I := by
  choose U hx hz using hl
  have hc : ⨆ x, (U x).1 = ⊤ := by
    apply top_unique
    intro x _
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hx x⟩
  have he : Scheme.IdealSheafData.ofIdealTop (Ideal.span {z}) ≤
      Scheme.IdealSheafData.ofIdealTop I := by
    apply Scheme.IdealSheafData.le_of_iSup_eq_top U hc
    intro x
    simp only [Scheme.IdealSheafData.ofIdealTop_ideal, Ideal.map_span, Set.image_singleton]
    exact (Ideal.span_singleton_le_iff_mem _).mpr (hz x)
  have ht : Ideal.span {z} ≤ I :=
    (map_le_map_iff (Scheme.IdealSheafData.equivOfIsAffine (X := X)).symm).mp he
  exact (Ideal.span_singleton_le_iff_mem _).mp ht

/-- The local test is an equivalence without any radical or reducedness hypothesis. -/
theorem mem_iff_neighborhoods : z ∈ I ↔
    ∀ x : X, ∃ U : X.affineOpens, x ∈ U.1 ∧
      X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op z ∈
        I.map (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op).hom := by
  refine ⟨?_, mem_of_neighborhoods I z⟩
  intro hz x
  exact ⟨⟨⊤, isAffineOpen_top X⟩, trivial, Ideal.mem_map_of_mem _ hz⟩

end FLT.Mazur.AffineIdealNeighborhoodMembership
