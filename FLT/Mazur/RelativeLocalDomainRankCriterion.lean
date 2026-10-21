/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeScalarLocalRankFiniteness
public import FLT.Mazur.RelativeRankCollisionValuations

/-!
# Generic and closed rank control the entire local-domain pullback

Every coefficient prime lies between the generic and closed points.
Monotonicity of original ranks forces all intermediate ranks to agree when
the two endpoint ranks agree. The full pullback is then finite by descent
from complete frames. Failure of finiteness has an actual strict rank drop.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  (b : Spec (.of R) ⟶ S)

omit [QuasiCompact E.hom] in
/-- Equal endpoint ranks bound the entire local-domain test, including all intermediate primes. -/
theorem range_exactRank_of_generic_closed (n : ℕ)
    (hg : b (⊥ : PrimeSpectrum R) ∈ exactRank E n)
    (hc : b (closedPoint R) ∈ exactRank E n) : Set.range b ⊆ exactRank E n := by
  rintro _ ⟨x, rfl⟩
  have hgx : (⊥ : PrimeSpectrum R) ⤳ x :=
    (PrimeSpectrum.le_iff_specializes _ _).mp bot_le
  refine ⟨((specializes_closedPoint x).map b.continuous).mem_open
    (rankImageOpen E n).isOpen hc.1, ?_⟩
  intro hx
  exact hg.2 ((hgx.map b.continuous).mem_open (rankImageOpen E (n + 1)).isOpen hx)

variable [LocallyQuasiFinite E.hom]

/-- A full original local-domain pullback is finite exactly when its two endpoint ranks agree. -/
theorem finite_local_pullback_iff_generic_closed :
    IsFinite (pullback.snd E.hom b) ↔ ∃ n,
      b (⊥ : PrimeSpectrum R) ∈ exactRank E n ∧ b (closedPoint R) ∈ exactRank E n := by
  constructor
  · intro hf
    let _ := hf
    obtain ⟨n, hn⟩ := exists_exactRank_local_of_finite E b
    exact ⟨n, hn (Set.mem_range_self _), hn (Set.mem_range_self _)⟩
  · rintro ⟨n, hg, hc⟩
    exact finite_pullback_of_exactRank E n b (range_exactRank_of_generic_closed E b n hg hc)

/-- Nonfiniteness is witnessed by a strict decrease between the actual generic and closed ranks. -/
theorem not_finite_local_pullback_iff_rank_drop :
    ¬ IsFinite (pullback.snd E.hom b) ↔ ∃ n m : ℕ, m < n ∧
      b (⊥ : PrimeSpectrum R) ∈ exactRank E n ∧ b (closedPoint R) ∈ exactRank E m := by
  constructor
  · intro hf
    obtain ⟨n, hn⟩ := exists_exactRank E (b (⊥ : PrimeSpectrum R))
    obtain ⟨m, hm⟩ := exists_exactRank E (b (closedPoint R))
    have hmn := exactRank_specialization_le E
      ((specializes_closedPoint (⊥ : PrimeSpectrum R)).map b.continuous) hn hm
    refine ⟨n, m, lt_of_le_of_ne hmn ?_, hn, hm⟩
    intro he
    apply hf
    exact (finite_local_pullback_iff_generic_closed E b).mpr ⟨n, hn, he ▸ hm⟩
  · rintro ⟨n, m, hmn, hn, hm⟩
    exact not_finite_pullback_of_rank_drop E b (specializes_closedPoint _) hn hm
      (Nat.ne_of_gt hmn)

end FLT.Mazur.RelativeOrderedTuples
