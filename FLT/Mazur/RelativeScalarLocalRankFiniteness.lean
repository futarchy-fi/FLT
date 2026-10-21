/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeFiniteRankSpecialization
public import FLT.Mazur.RelativeExactRankFinite

/-!
# Finiteness and exact rank on full local coefficient schemes

Over an arbitrary local ring, finiteness of the full original pullback is
equivalent to constant original rank. The reverse direction uses the existing
complete-frame cover and descends finiteness; the forward direction uses
specialization to the unique closed point. No reducedness or flatness is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
namespace FLT.Mazur.RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S : Scheme.{0}} (E : Over S) [Etale E.hom] [IsSeparated E.hom]
  [QuasiCompact E.hom] {R : Type} [CommRing R] [IsLocalRing R]
  (b : Spec (.of R) ⟶ S)

/-- A full finite local pullback has the same original rank at every coefficient prime. -/
theorem exactRank_local_iff_closedPoint [IsFinite (pullback.snd E.hom b)]
    (x : Spec (.of R)) (n : ℕ) :
    b x ∈ exactRank E n ↔ b (closedPoint R) ∈ exactRank E n :=
  exactRank_specializes_iff_of_finite_pullback E b (specializes_closedPoint x) n

/-- Finiteness constructs a single exact rank for the entire unchanged local test scheme. -/
theorem exists_exactRank_local_of_finite [IsFinite (pullback.snd E.hom b)] :
    ∃ n, Set.range b ⊆ exactRank E n := by
  obtain ⟨n, hn⟩ := exists_exactRank E (b (closedPoint R))
  refine ⟨n, ?_⟩
  rintro _ ⟨x, rfl⟩
  exact (exactRank_local_iff_closedPoint E b x n).mpr hn

variable [LocallyQuasiFinite E.hom]

/-- Full local finiteness is exactly constancy of the original geometric rank. -/
theorem finite_local_pullback_iff_constant_rank :
    IsFinite (pullback.snd E.hom b) ↔ ∃ n, Set.range b ⊆ exactRank E n := by
  constructor
  · intro hf
    let _ := hf
    exact exists_exactRank_local_of_finite E b
  · rintro ⟨n, hn⟩
    exact finite_pullback_of_exactRank E n b hn

/-- The actual closed rank determines the full local finiteness test. -/
theorem finite_local_pullback_iff_closed_rank (n : ℕ)
    (hn : b (closedPoint R) ∈ exactRank E n) :
    IsFinite (pullback.snd E.hom b) ↔ Set.range b ⊆ exactRank E n := by
  constructor
  · intro hf
    let _ := hf
    rintro _ ⟨x, rfl⟩
    exact (exactRank_local_iff_closedPoint E b x n).mpr hn
  · exact finite_pullback_of_exactRank E n b

end FLT.Mazur.RelativeOrderedTuples
