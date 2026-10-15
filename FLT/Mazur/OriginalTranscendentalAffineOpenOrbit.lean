/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalTensorOrbitEvaluation
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Full algebraic point orbits in the unchanged extended affine spectrum

A finite family of nonempty opens in Spec(K tensor_k A) contains every
k-conjugate of one algebraic A-point. This retains the actual larger-field
opens and the original affine coordinate algebra. No finite orbit of these
opens or algebraic descent of their defining conditions is assumed.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
open scoped TensorProduct
variable {k L K A J : Type*} [Field k] [Field L] [Field K]
  [Algebra k L] [Algebra L K] [Algebra k K] [IsScalarTower k L K]
  [Algebra.IsAlgebraic k L] [IsAlgClosed L]
  [CommRing A] [Algebra k A] [Algebra.FiniteType k A]
  [IsDomain (L ⊗[k] A)] [Finite J]

/-- The actual extended point determined by a conjugate of an original algebraic point. -/
def originalExtendedPoint (q : A →ₐ[k] L) (σ : L ≃ₐ[k] L) : PrimeSpectrum (K ⊗[k] A) :=
  ⟨RingHom.ker (originalEvaluation (K := K) q σ), RingHom.ker_isPrime _⟩

/-- One algebraic point works, with every conjugate, for every prescribed nonempty extended open. -/
theorem exists_original_point_orbit_in_opens
    (U : J → TopologicalSpace.Opens (PrimeSpectrum (K ⊗[k] A)))
    (hU : ∀ j, (U j : Set (PrimeSpectrum (K ⊗[k] A))).Nonempty) :
    ∃ q : A →ₐ[k] L, ∀ (σ : L ≃ₐ[k] L) (j : J),
      originalExtendedPoint (K := K) q σ ∈ U j := by
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
  obtain ⟨q, hq⟩ := exists_original_point_all_conjugates (L := L) x hx
  exact ⟨q, fun σ j ↦ hsub j (hq σ j)⟩

end FLT.Mazur.TranscendentalCoefficientOrbitAvoidance
