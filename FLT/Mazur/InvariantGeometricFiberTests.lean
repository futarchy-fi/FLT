/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ScalarAlgebraicClosureTests
public import FLT.Mazur.FiniteGroupQuotientGeometricPoints

/-!
# Original geometric source points detect invariant fiber tests

Every point of the invariant algebra over the fixed residue closure lifts to
the original coordinate algebra. The original scalar triangle is retained.
Thus tests can be established on actual source points, without choosing an
invariant-ring presentation or imposing a tame-characteristic assumption.
-/

@[expose] public noncomputable section
universe u
namespace FLT.Mazur.FiniteGroupQuotient
open ScalarTestLocalization
variable (G A : Type u) [Group G] [Finite G] [CommRing A] [MulSemiringAction G A]
  {R : Type u} [CommRing R] (s : R →+* invariantRing G A) (P : PrimeSpectrum R)
local notation "K" => AlgebraicClosure P.asIdeal.ResidueField
local notation "i" => inclusion G A

/-- Lift a specified invariant geometric point while retaining its original scalar triangle. -/
theorem exists_source_residue_point (v : invariantRing G A →+* K)
    (hv : v.comp s = algebraMap R K) :
    ∃ w : A →+* K, w.comp i = v ∧ w.comp ((i).comp s) = algebraMap R K := by
  let _ := Algebra.IsInvariant.isIntegral (invariantRing G A) A G
  obtain ⟨w, hw⟩ := exists_ringHom_of_integral (invariantRing G A) A v
  change w.comp i = v at hw
  exact ⟨w, hw, by rw [← RingHom.comp_assoc, hw, hv]⟩

/-- Invariant geometric tests are detected by original source points with the same scalars. -/
theorem residueGeometricTest_iff_source_values (b : invariantRing G A) :
    residueGeometricTest s P b ↔ ∀ w : A →+* K,
      w.comp ((i).comp s) = algebraMap R K → w (i b) = 0 := by
  rw [residueGeometricTest_iff]
  constructor
  · intro h w hw
    exact h (w.comp i) (by simpa only [RingHom.comp_assoc] using hw)
  · intro h v hv
    obtain ⟨w, hw, hs⟩ := exists_source_residue_point G A s P v hv
    exact (DFunLike.congr_fun hw b).symm.trans (h w hs)

/-- A failed original invariant fiber test constructs an actual source-valued witness. -/
theorem exists_source_residue_failure (hs : s.FiniteType) (b : invariantRing G A)
    (q : PrimeSpectrum (invariantRing G A)) (hq : PrimeSpectrum.comap s q = P)
    (hb : b ∉ q.asIdeal) :
    ∃ w : A →+* K, w.comp ((i).comp s) = algebraMap R K ∧ w (i b) ≠ 0 := by
  obtain ⟨v, hv, hb⟩ := exists_residue_geometric_failure s P hs b q hq hb
  obtain ⟨w, hw, hs⟩ := exists_source_residue_point G A s P v hv
  refine ⟨w, hs, ?_⟩
  simpa only [← DFunLike.congr_fun hw b, RingHom.comp_apply] using hb

end FLT.Mazur.FiniteGroupQuotient
