/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGeneratorSpan
public import Mathlib.AlgebraicGeometry.Limits

/-!
# Finite coordinates for a section cover

Adding one zero section allows any finite family, including the empty
family, to be indexed by `Fin (n + 1)`. Its generator union is unchanged
and affine inverse-image generator opens are preserved.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

/-- Reindex a finite section family by projective coordinates, adding only an empty open. -/
theorem exists_fin_section_family {X : Scheme.{u}} (M : X.Modules)
    {ι : Type u} [Finite ι] (a : ι → Γ(M, ⊤)) :
    ∃ (n : ℕ) (t : Fin (n + 1) → Γ(M, ⊤)),
      (⨆ k, sectionGeneratorOpen M (t k)) = ⨆ i, sectionGeneratorOpen M (a i) ∧
      (∀ k, t k = 0 ∨ ∃ i, t k = a i) := by
  classical
  let _ := Fintype.ofFinite ι
  let n := Fintype.card ι
  let e : Option ι ≃ Fin (n + 1) := Fintype.equivOfCardEq (by simp [n])
  let v : Option ι → Γ(M, ⊤) := fun i ↦ i.elim 0 a
  let t : Fin (n + 1) → Γ(M, ⊤) := fun k ↦ v (e.symm k)
  have hcases (k : Fin (n + 1)) : t k = 0 ∨ ∃ i, t k = a i := by
    cases h : e.symm k with
    | none => exact Or.inl (by simp [t, v, h])
    | some i => exact Or.inr ⟨i, by simp [t, v, h]⟩
  refine ⟨n, t, le_antisymm ?_ ?_, hcases⟩
  · apply iSup_le
    intro k
    rcases hcases k with h | ⟨i, h⟩
    · rw [h, sectionGeneratorOpen_zero]
      exact bot_le
    · rw [h]
      exact le_iSup (fun i ↦ sectionGeneratorOpen M (a i)) i
  · apply iSup_le
    intro i
    have ht : t (e (some i)) = a i := by simp [t, v]
    rw [← ht]
    exact le_iSup (fun k ↦ sectionGeneratorOpen M (t k)) (e (some i))

/-- The coordinate reindexing preserves affineness of generator opens on any test scheme. -/
theorem exists_fin_affine_section_family {X Y : Scheme.{u}} (M : X.Modules) (j : Y ⟶ X)
    {ι : Type u} [Finite ι] (a : ι → Γ(M, ⊤))
    (ha : ∀ i, IsAffineOpen (j ⁻¹ᵁ sectionGeneratorOpen M (a i))) :
    ∃ (n : ℕ) (t : Fin (n + 1) → Γ(M, ⊤)),
      (⨆ k, sectionGeneratorOpen M (t k)) = ⨆ i, sectionGeneratorOpen M (a i) ∧
      ∀ k, IsAffineOpen (j ⁻¹ᵁ sectionGeneratorOpen M (t k)) := by
  obtain ⟨n, t, ht, hcases⟩ := exists_fin_section_family M a
  refine ⟨n, t, ht, fun k ↦ ?_⟩
  rcases hcases k with h | ⟨i, h⟩
  · rw [h, sectionGeneratorOpen_zero]
    exact isAffineOpen_bot Y
  · rw [h]
    exact ha i

end FLT.Mazur.FCurve
