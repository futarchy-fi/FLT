/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationCompleteExactRank
public import FLT.Mazur.EquivalenceRelationNormalizedFrameLifts
public import FLT.Mazur.EquivalenceRelationScalarDefectCharacters

/-!
# Incomplete frames extend to strictly larger complete original frames

The endpoint and coefficient field stay fixed. A uniform original rank bound
bounds the extension size on a Noetherian endpoint scheme. This supplies the
rank-growth step for repairing an incomplete scalar-character chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme} {p q : D ⟶ A} [IsSeparated p] [Etale p] [QuasiCompact p]
  (e : CategoryTheory.EquivalenceRelation p q)
local instance growthOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance growthOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance growthOver_quasiCompact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

include e in
/-- Incompleteness produces a strictly larger complete frame over the same geometric endpoint. -/
theorem exists_strictly_larger_complete_frame {K : Type} [Field K] [IsSepClosed K]
    (n : ℕ) (o : Fin n) (u : Spec (.of K) ⟶ source p q (Fin n) o)
    (hu : ¬ Complete (Fin n) o u) :
    ∃ (m : ℕ) (j : Fin m) (v : Spec (.of K) ⟶ source p q (Fin m) j),
      n < m ∧ v ≫ first p q (Fin m) j = u ≫ first p q (Fin n) o ∧
        Complete (Fin m) j v := by
  obtain ⟨m, j, v, hv, hc⟩ := exists_complete_normalized_lift e (u ≫ first p q (Fin n) o)
  refine ⟨m, j, v, ?_, hv, hc⟩
  by_contra hn
  have hb := rankAtMost_mono (Over.mk p) (Nat.le_of_not_gt hn)
    ((complete_iff_endpoint_rankAtMost m j v).mp hc)
  apply hu
  apply (complete_iff_endpoint_rankAtMost n o u).mpr
  change (v ≫ first p q (Fin m) j) default ∈ rankAtMost (Over.mk p) n at hb
  rw [hv] at hb
  exact hb

include e in
/-- A single constructed bound controls all such complete extensions on a Noetherian base. -/
theorem exists_bounded_complete_frame_growth [TopologicalSpace.NoetherianSpace A] :
    ∃ N : ℕ, ∀ {K : Type} [Field K] [IsSepClosed K],
      ∀ (n : ℕ) (o : Fin n) (u : Spec (.of K) ⟶ source p q (Fin n) o),
        ¬ Complete (Fin n) o u →
        ∃ (m : ℕ) (j : Fin m) (v : Spec (.of K) ⟶ source p q (Fin m) j),
          n < m ∧ m ≤ N ∧ v ≫ first p q (Fin m) j = u ≫ first p q (Fin n) o ∧
            Complete (Fin m) j v := by
  obtain ⟨N, hN⟩ := exists_uniform_rank_bound (Over.mk p)
  refine ⟨N, ?_⟩
  intro K _ _ n o u hu
  obtain ⟨m, j, v, hm, hv, hc⟩ := exists_strictly_larger_complete_frame e n o u hu
  refine ⟨m, j, v, hm, hN ((v ≫ first p q (Fin m) j) default) m ?_, hv, hc⟩
  exact ⟨(testFrame (Fin m) j v).left (default : Spec (.of K)),
    congrArg (fun f : Spec (.of K) ⟶ A ↦ f default) (testFrame (Fin m) j v).w⟩

open FiniteGroupRestriction SchemeFiniteGroupQuotient SchemeScalarPrincipalNeighborhood
variable (n : ℕ) (o : Fin n) (B : (source p q (Fin n) o).Opens)
  (hB : ∀ g : Equiv.Perm (Fin n), (action e (Fin n) o g).hom ⁻¹ᵁ B = B)
  [IsAffine B.toScheme]
local notation "ρ" => restrictedAction (action e (Fin n) o) B hB
variable {R : Type} [CommRing R]
  (σ : R →+* invariantCoordinates (restrictedAction (action e (Fin n) o) B hB))
local notation "s" => invariantScalarCoordinates ρ σ
local notation "K" P => scalarResidueClosure P
attribute [local irreducible] source action restrictedAction Complete

/-- Every actual excluded scalar prime constructs a bounded larger complete replacement frame. -/
theorem exists_bounded_scalar_defect_extensions [TopologicalSpace.NoetherianSpace A]
    (hs : σ.FiniteType) :
    ∃ N : ℕ, ∀ P : PrimeSpectrum R,
      P ∈ Set.range (PrimeSpectrum.comap σ) →
      P ∉ wholeCompleteScalarLocus e (Fin n) o B hB σ →
      ∃ w : Γ(B.toScheme, ⊤) →+* K P,
        w.comp s = algebraMap R (K P) ∧
        ¬ Complete (Fin n) o (sourceCharacterMap w ≫ B.ι) ∧
        ∃ (m : ℕ) (j : Fin m) (v : Spec (.of (K P)) ⟶ source p q (Fin m) j),
          n < m ∧ m ≤ N ∧
          v ≫ first p q (Fin m) j = sourceCharacterMap w ≫ B.ι ≫ first p q (Fin n) o ∧
          Complete (Fin m) j v := by
  obtain ⟨N, hN⟩ := exists_bounded_complete_frame_growth e
  refine ⟨N, fun P hr hP ↦ ?_⟩
  obtain ⟨w, hw, hn, _⟩ := exists_incomplete_scalar_defect_character
    e (Fin n) o B hB σ hs P hr hP
  obtain ⟨m, j, v, hm, hmN, hv, hc⟩ := hN n o (sourceCharacterMap w ≫ B.ι) hn
  exact ⟨w, hw, hn, m, j, v, hm, hmN, by simpa only [Category.assoc] using hv, hc⟩

end FLT.Mazur.EquivalenceRelationNormalizedFrames
