/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRankCollisionGenerizations
public import FLT.Mazur.SchemeValuationImageClosure

/-!
# Valuation witnesses and rank drops for actual collisions

Constructible compactness constructs a valuation square at every scalar
rank-obstruction point. Its generic pair has actual unequal exact ranks.
A lift with equal-rank closed endpoints necessarily drops at least one
endpoint rank; existence of a lift alone does not exclude collisions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace IsLocalRing
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {A T : Scheme.{0}} (E : Over A) [Etale E.hom] [IsSeparated E.hom]

/-- Original exact rank can only decrease along specialization. -/
theorem exactRank_specialization_le {a b : A} (hab : a ⤳ b) {n m : ℕ}
    (ha : a ∈ exactRank E n) (hb : b ∈ exactRank E m) : m ≤ n := by
  by_contra h
  have hm : n + 1 ≤ m := Nat.lt_of_not_ge h
  exact ha.2 (rankImageOpen_antitone E hm
    (hab.mem_open (rankImageOpen E m).isOpen hb.1))

variable (x y : T ⟶ A) {R : Type} [CommRing R] (s : T ⟶ Spec (.of R))

/-- Matching lifted endpoints force a strict rank drop from a colliding generic pair. -/
theorem rankCollision_square_lift_rank_drop (V : ValuativeCommSq s)
    (hV : V.i₁ default ∈ rankCollision E x y) (l : V.commSq.LiftStruct)
    (k : ℕ) (hx : x (l.l (closedPoint V.R)) ∈ exactRank E k)
    (hy : y (l.l (closedPoint V.R)) ∈ exactRank E k) :
    ∃ n : ℕ, k < n ∧
      (x (V.i₁ default) ∈ exactRank E n ∨ y (V.i₁ default) ∈ exactRank E n) := by
  obtain ⟨n, m, hnm, hn, hm⟩ := hV
  have ht := (SchemeSpecializationValuation.lift_specializes s V l).1
  have hkn := exactRank_specialization_le E (ht.map x.continuous) hn hx
  have hkm := exactRank_specialization_le E (ht.map y.continuous) hm hy
  by_cases h : k < n
  · exact ⟨n, h, Or.inl hn⟩
  · have hnk : n = k := Nat.le_antisymm (Nat.le_of_not_gt h) hkn
    have hkm' : k < m := lt_of_le_of_ne hkm (fun he ↦ hnm (hnk.trans he))
    exact ⟨m, hkm', Or.inr hm⟩

variable [QuasiCompact E.hom] [NoetherianSpace A] [CompactSpace T] [QuasiSeparatedSpace T]
  [QuasiCompact x] [QuasiCompact y] [QuasiCompact s]

/-- The scalar obstruction is exactly existence of a colliding valuative generic pair. -/
theorem rankCollisionIdeal_le_iff_valuation (P : PrimeSpectrum R) :
    rankCollisionIdeal E x y s ≤ P.asIdeal ↔
      ∃ V : ValuativeCommSq s, V.i₁ default ∈ rankCollision E x y ∧
        V.i₂ (closedPoint V.R) = P := by
  rw [rankCollisionIdeal_le_iff_generizing_collision]
  constructor
  · rintro ⟨t, ht, htP⟩
    obtain ⟨V, hV, hP⟩ := SchemeSpecializationValuation.exists_square s t P
      ((PrimeSpectrum.le_iff_specializes _ _).mp htP)
    exact ⟨V, hV.symm ▸ ht, hP⟩
  · rintro ⟨V, hV, rfl⟩
    exact ⟨V.i₁ default, hV, (PrimeSpectrum.le_iff_specializes _ _).mpr
      (SchemeSpecializationValuation.square_specializes s V)⟩

/-- Rank agreement on valuative generic pairs is an exact criterion for a principal neighborhood. -/
theorem rankCollisionIdeal_not_le_iff_valuative_ranks (P : PrimeSpectrum R) :
    ¬ rankCollisionIdeal E x y s ≤ P.asIdeal ↔
      ∀ V : ValuativeCommSq s, V.i₂ (closedPoint V.R) = P →
        ∃ n, x (V.i₁ default) ∈ exactRank E n ∧ y (V.i₁ default) ∈ exactRank E n := by
  rw [rankCollisionIdeal_le_iff_valuation]
  constructor
  · intro h V hP
    exact (not_mem_rankCollision_iff E x y _).mp (fun ht ↦ h ⟨V, ht, hP⟩)
  · rintro h ⟨V, hV, hP⟩
    exact (not_mem_rankCollision_iff E x y _).mpr (h V hP) hV

end FLT.Mazur.RelativeOrderedTuples
