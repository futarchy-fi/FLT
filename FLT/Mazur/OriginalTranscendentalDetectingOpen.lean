/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalTranscendentalAffineOpenOrbit

/-!
# A nonempty algebraic coefficient condition controlling actual extended opens

Keep the detecting condition before choosing a point. Every L-rational point
satisfying it has its whole conjugacy orbit in the unchanged K-opens. This
allows a subsequent smooth étale construction to choose a separable point.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
open scoped TensorProduct
variable {k L K A J : Type*} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] [CommRing A] [Algebra k A]
  [IsDomain (L ⊗[k] A)] [Finite J]

/-- The original algebraic principal condition works uniformly before a point is chosen. -/
theorem exists_original_detecting_condition
    (U : J → TopologicalSpace.Opens (PrimeSpectrum (K ⊗[k] A)))
    (hU : ∀ j, (U j : Set (PrimeSpectrum (K ⊗[k] A))).Nonempty) :
    ∃ a : L ⊗[k] A, a ≠ 0 ∧ ∀ p : L ⊗[k] A →ₐ[L] L,
      p a ≠ 0 → ∀ (σ : L ≃ₐ[k] L) (j : J),
        originalExtendedPoint (K := K)
          ((p.restrictScalars k).comp Algebra.TensorProduct.includeRight) σ ∈ U j := by
  classical
  have hb (j : J) : ∃ x : K ⊗[k] A, x ≠ 0 ∧
      PrimeSpectrum.basicOpen x ≤ U j := by
    obtain ⟨v, ⟨x, rfl⟩, hv, hsub⟩ :=
      PrimeSpectrum.isTopologicalBasis_basic_opens.exists_nonempty_subset (hU j) (U j).isOpen
    refine ⟨x, ?_, hsub⟩
    rintro rfl
    simp only [PrimeSpectrum.basicOpen_zero, TopologicalSpace.Opens.coe_bot,
      Set.not_nonempty_empty] at hv
  choose x hx hsub using hb
  let e := Algebra.TensorProduct.cancelBaseChange k L K K A
  obtain ⟨a, ha, hd⟩ := exists_orbit_detecting_coefficient (fun j ↦ e.symm (x j))
    (fun j h ↦ hx j (e.symm.injective (h.trans (map_zero _).symm)))
  refine ⟨a, ha, fun p hp σ j ↦ hsub j ?_⟩
  have h := hd p hp σ j
  rw [evaluation_cancel] at h
  exact h

end FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
