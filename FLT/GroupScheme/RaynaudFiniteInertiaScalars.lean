/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudTameQuotientScalars
public import FLT.AbsoluteGaloisGroup.FiniteTameQuotient

/-!
# Constructed scalar fields for simple finite inertia representations

For a faithful finite action on a DVR with finite residue field, first
ramification is a p-group and the tame character embeds its quotient into
residue units. These proved facts give the scalar field of each simple factor.
-/

@[expose] public noncomputable section
namespace LocalRamification
open IsLocalRing

universe v
variable (R G : Type*) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Group G] [Finite G] [MulSemiringAction G R] [FaithfulSMul G R]
  [Finite (ResidueField R)] (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]
  {V : Type v} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  (ρ : Representation (ZMod p) (ramificationGroup R G 0) V) [ρ.IsIrreducible]

/-- A simple finite inertia representation is a line over a derived finite scalar field. -/
theorem exists_rank_one_scalar_field_of_finite_inertia :
    ∃ (F : Type v) (_ : Field F) (_ : Finite F) (_ : CharP F p) (_ : Module F V),
      Module.finrank F V = 1 ∧ ∀ (a : F) (g : ramificationGroup R G 0) (x : V),
        ρ g (a • x) = a • ρ g x := by
  let I := ramificationGroup R G 0
  let N := (firstGroup R G).comap I.subtype
  have hN : IsPGroup p N := (firstGroup_isPGroup R G p).comap_subtype
  apply ρ.exists_rank_one_scalar_field_of_tame_quotient N
  · exact hN.of_surjective (ρ.toHomUnits.comp N.subtype).rangeRestrict
      (ρ.toHomUnits.comp N.subtype).rangeRestrict_surjective
  · obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible R
    intro a b
    apply (finiteTameQuotientEmbedding_injective R G hπ)
    simp only [map_mul, mul_comm]

end LocalRamification
