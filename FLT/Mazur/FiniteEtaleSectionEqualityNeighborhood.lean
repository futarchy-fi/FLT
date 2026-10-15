/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UnramifiedSectionImmersion
public import Mathlib.AlgebraicGeometry.Morphisms.Separated

/-!
# Constant equality patterns for finite étale sections

The coincidence locus of two sections of a separated étale morphism is
clopen. A finite family therefore has a constant coincidence pattern on
an actual affine neighborhood of any specified base point.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.FiniteEtaleSectionEqualityNeighborhood
universe u
variable {X Y : Scheme.{u}} (p : X ⟶ Y) [Etale p] [IsSeparated p]

/-- Coincidence of two actual étale sections is a clopen condition on the original base. -/
theorem isClopen_coincidence (s t : Y ⟶ X)
    (hs : s ≫ p = 𝟙 Y) (ht : t ≫ p = 𝟙 Y) :
    IsClopen {y : Y | s y = t y} := by
  let _ := UnramifiedSectionImmersion.isOpenImmersion p t ht
  let _ : IsClosedImmersion (t ≫ p) := by rw [ht]; infer_instance
  let _ : IsClosedImmersion t := IsClosedImmersion.of_comp t p
  have he : {y : Y | s y = t y} = s ⁻¹' Set.range t := by
    ext y
    constructor
    · intro h
      exact ⟨y, h.symm⟩
    · rintro ⟨z, hz⟩
      have hzy : z = y := by
        have h := congrArg p hz
        change (t ≫ p) z = (s ≫ p) y at h
        rw [ht, hs] at h
        exact h
      exact (hzy ▸ hz).symm
  rw [he]
  exact ⟨t.isClosedEmbedding.isClosed_range.preimage s.continuous,
    t.isOpenEmbedding.isOpen_range.preimage s.continuous⟩

/-- Every finite section family has a constant equality pattern near each original base point. -/
theorem exists_affine_constant_pattern {ι : Type*} [Finite ι]
    (s : ι → (Y ⟶ X)) (hs : ∀ i, s i ≫ p = 𝟙 Y) (y : Y) :
    ∃ W : Y.Opens, IsAffineOpen W ∧ y ∈ W ∧
      ∀ i j, ∀ x ∈ W, s i x = s j x ↔ s i y = s j y := by
  classical
  let E (i j : ι) : Set Y := {x | s i x = s j x}
  let O (i j : ι) : Set Y := if s i y = s j y then E i j else (E i j)ᶜ
  have ho (i j : ι) : IsOpen (O i j) := by
    dsimp only [O]
    split
    · exact (isClopen_coincidence p (s i) (s j) (hs i) (hs j)).2
    · exact (isClopen_coincidence p (s i) (s j) (hs i) (hs j)).1.isOpen_compl
  let U : Y.Opens := ⟨⋂ i, ⋂ j, O i j,
    isOpen_iInter_of_finite fun i ↦ isOpen_iInter_of_finite (ho i)⟩
  have hy : y ∈ U := by
    simp only [U, TopologicalSpace.Opens.mem_mk, Set.mem_iInter]
    intro i j
    by_cases h : s i y = s j y <;> simp [O, E, h]
  obtain ⟨W, hW, hyW, hWU⟩ := exists_isAffineOpen_mem_and_subset hy
  refine ⟨W, hW, hyW, fun i j x hx ↦ ?_⟩
  have hxO : x ∈ O i j := Set.mem_iInter.mp (Set.mem_iInter.mp (hWU hx) i) j
  by_cases h : s i y = s j y
  · have he : s i x = s j x := by
      simpa only [O, ite_eq_left h, E, Set.mem_ofPred_eq] using hxO
    exact iff_of_true he h
  · have he : s i x ≠ s j x := by
      simpa only [O, ite_eq_right h, E, Set.mem_compl_iff, Set.mem_ofPred_eq] using hxO
    exact iff_of_false he h

end FLT.Mazur.FiniteEtaleSectionEqualityNeighborhood
