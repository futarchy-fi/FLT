/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankCollisionGenerizations
public import Mathlib.AlgebraicGeometry.Stalk

/-!
# Full scalar-local tests for collision-free principal neighborhoods

The test is the entire pullback to the original scalar local scheme, with
all nilpotents retained. Its points represent exactly all generizing scalar
centers. Rank agreement on this whole scheme constructs a denominator.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {T : Scheme.{0}} {R : Type} [CommRing R] (s : T ⟶ Spec (.of R))
  (P : PrimeSpectrum R)

/-- The full test scheme over the stalk of the unchanged original scalar spectrum. -/
def rankScalarLocalTest : Scheme := pullback s ((Spec (.of R)).fromSpecStalk P)

/-- The actual projection to the original test scheme. -/
def rankScalarLocalMap : rankScalarLocalTest s P ⟶ T := pullback.fst _ _

/-- Every generizing scalar center has an actual point of the full localized test. -/
theorem rankScalarLocalMap_range :
    Set.range (rankScalarLocalMap s P) = {t : T | (s t).asIdeal ≤ P.asIdeal} := by
  let ι := (Spec (.of R)).fromSpecStalk P
  ext t
  constructor
  · rintro ⟨u, rfl⟩
    apply (PrimeSpectrum.le_iff_specializes _ _).mpr
    have h : s (rankScalarLocalMap s P u) ∈ Set.range ι := by
      refine ⟨pullback.snd s ι u, ?_⟩
      exact (congrArg (fun f ↦ f u) (pullback.condition (f := s) (g := ι))).symm
    rwa [Scheme.range_fromSpecStalk] at h
  · intro ht
    have h : s t ∈ Set.range ι := by
      rw [Scheme.range_fromSpecStalk]
      exact (PrimeSpectrum.le_iff_specializes _ _).mp ht
    obtain ⟨z, hz⟩ := h
    obtain ⟨u, hu, _⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := s) (g := ι) t z hz.symm
    exact ⟨u, hu⟩

variable {A : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] [NoetherianSpace A] [CompactSpace T] [QuasiSeparatedSpace T]
  (x y : T ⟶ A) [QuasiCompact x] [QuasiCompact y] [QuasiCompact s]

/-- A collision-free full local test is precisely exclusion of the original obstruction ideal. -/
theorem rankCollisionIdeal_not_le_iff_local_ranks :
    ¬ rankCollisionIdeal E x y s ≤ P.asIdeal ↔
      ∀ u : rankScalarLocalTest s P,
        ∃ n, x (rankScalarLocalMap s P u) ∈ exactRank E n ∧
          y (rankScalarLocalMap s P u) ∈ exactRank E n := by
  rw [rankCollisionIdeal_not_le_iff_generizing_ranks]
  constructor
  · intro h u
    apply h
    have hu := Set.mem_range_self (f := rankScalarLocalMap s P) u
    rwa [rankScalarLocalMap_range] at hu
  · intro h t ht
    have ht' : t ∈ Set.range (rankScalarLocalMap s P) := by
      rw [rankScalarLocalMap_range]
      exact ht
    obtain ⟨u, rfl⟩ := ht'
    exact h u

/-- Whole-local rank agreement spreads to one original principal neighborhood. -/
theorem exists_same_rank_principal_of_local_ranks
    (h : ∀ u : rankScalarLocalTest s P,
      ∃ n, x (rankScalarLocalMap s P u) ∈ exactRank E n ∧
        y (rankScalarLocalMap s P u) ∈ exactRank E n) :
    ∃ r : R, r ∉ P.asIdeal ∧
      ∀ t : T, s t ∈ PrimeSpectrum.basicOpen r →
        ∃ n, x t ∈ exactRank E n ∧ y t ∈ exactRank E n :=
  (rankCollisionIdeal_not_le_iff E x y s P).mp
    ((rankCollisionIdeal_not_le_iff_local_ranks s P E x y).mpr h)

end FLT.Mazur.RelativeOrderedTuples
