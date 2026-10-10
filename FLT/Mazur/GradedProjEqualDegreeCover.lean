/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper

/-!
# Finite equal-degree covers of a finite-type Proj

Raise a finite homogeneous generating family to a common positive degree.
Taking powers leaves its basic opens unchanged.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

universe u

namespace FLT.Mazur.GradedProjEqualDegreeCover

variable {A : Type u} [CommRing A] {σ : Type*} [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] [Algebra.FiniteType (𝒜 0) A]

/-- Finite homogeneous coordinates together with their proved covering property. -/
structure Coordinates where
  /-- The finite indexing type. -/
  Index : Type u
  /-- The chosen finite enumeration. -/
  finiteIndex : Fintype Index
  /-- Their common homogeneous degree. -/
  degree : ℕ
  /-- The common degree is positive. -/
  positive : 0 < degree
  /-- The original homogeneous elements. -/
  coordinate : Index → A
  /-- All coordinates have the same degree. -/
  homogeneous : ∀ i, coordinate i ∈ 𝒜 degree
  /-- Their basic opens cover the original Proj. -/
  covers : (⨆ i, Proj.basicOpen 𝒜 (coordinate i)) = ⊤

/-- A finite-type graded algebra admits a finite Proj cover in one positive degree. -/
theorem exists_cover : ∃ (ι : Type u) (_ : Fintype ι) (d : ℕ), 0 < d ∧
    ∃ f : ι → A, (∀ i, f i ∈ 𝒜 d) ∧ (⨆ i, Proj.basicOpen 𝒜 (f i)) = ⊤ := by
  classical
  obtain ⟨s, hs, hs'⟩ := GradedAlgebra.exists_finset_adjoin_eq_top_and_homogeneous_ne_zero 𝒜
  choose d hd hf using fun i : s ↦ hs' i i.2
  let q := ∏ i : s, d i
  have hq : 0 < q := Finset.prod_pos (fun i _ ↦ Nat.pos_of_ne_zero (hd i))
  have hdiv (i : s) : d i ∣ q := Finset.dvd_prod_of_mem d (Finset.mem_univ i)
  have hpos (i : s) : 0 < q / d i :=
    Nat.div_pos (Nat.le_of_dvd hq (hdiv i)) (Nat.pos_of_ne_zero (hd i))
  refine ⟨s, inferInstance, q, hq, fun i ↦ (i : A) ^ (q / d i), ?_, ?_⟩
  · intro i
    have hm := SetLike.pow_mem_graded (q / d i) (hf i)
    simpa only [nsmul_eq_mul, Nat.cast_id, Nat.div_mul_cancel (hdiv i)] using hm
  · simp only [Proj.basicOpen_pow 𝒜 _ _ (hpos _)]
    exact Proj.iSup_basicOpen_eq_top' 𝒜 (ι := s) (↑)
      (fun i ↦ ⟨d i, hf i⟩) (by simpa using hs)

/-- The coordinate data exists without any additional generation hypothesis. -/
theorem nonempty_coordinates : Nonempty (Coordinates 𝒜) := by
  obtain ⟨ι, hι, d, hd, f, hf, hc⟩ := exists_cover 𝒜
  exact ⟨⟨ι, hι, d, hd, f, hf, hc⟩⟩

end FLT.Mazur.GradedProjEqualDegreeCover
