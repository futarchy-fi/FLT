/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.InertiaDescentHenselian
public import FLT.AbsoluteGaloisGroup.TameRootIntegralModel
public import FLT.GroupScheme.RaynaudHenselianCharacters

/-!
# Integral roots of unity for the tame-root field

A finite residue field supplies a primitive root of order q - 1. Hensel's
lemma lifts it to the integer ring. For the rational completion the required
completeness is proved, including at two.
-/

@[expose] public noncomputable section
open IsLocalRing
namespace LocalRoot

/-- A Henselian local ring with finite residue field contains the full tame roots of unity. -/
theorem exists_primitive_tame_root {R : Type*} [CommRing R]
    [HenselianLocalRing R] [Finite (ResidueField R)] :
    ∃ z : R, IsPrimitiveRoot z (Nat.card (ResidueField R) - 1) := by
  let k := ResidueField R
  let : Fintype k := Fintype.ofFinite k
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := kˣ)
  have hu' : IsPrimitiveRoot (u : k) (Nat.card k - 1) := by
    rw [← Nat.card_units, ← hu]
    exact (IsPrimitiveRoot.coe_units_iff).mpr (IsPrimitiveRoot.orderOf u)
  have hn : ((Nat.card k - 1 : ℕ) : k) ≠ 0 := by
    rw [Nat.cast_sub (Nat.succ_le_of_lt (Nat.card_pos (α := k))),
      Nat.card_eq_fintype_card, Nat.cast_card_eq_zero]
    norm_num
  obtain ⟨z, hz, _⟩ := ThreeAdicPlan.henselian_lift_primitiveRoot hn (u : k) hu'
  exact ⟨z, hz⟩

/-- Completeness at the maximal ideal implies the local Hensel property. -/
theorem henselian_of_adicComplete (R : Type*) [CommRing R] [IsLocalRing R]
    [IsAdicComplete (maximalIdeal R) R] : HenselianLocalRing R := by
  constructor
  intro f hf x hx hd
  exact HenselianRing.is_henselian f hf x hx
    (hd.map (Ideal.Quotient.mk (maximalIdeal R)))

/-- The actual rational completion integers are Henselian. -/
theorem rationalCompletionIntegers_henselian (p : ℕ) [Fact p.Prime] :
    HenselianLocalRing
      ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ) := by
  let := rationalCompletionIntegers_adicComplete p
  exact henselian_of_adicComplete _

/-- Primitive tame roots exist in the rational local field without an added root hypothesis. -/
theorem rationalCompletion_exists_primitive_tame_root (p : ℕ) [Fact p.Prime] :
    ∃ z : (LocalCyclotomic.rationalPlace p).adicCompletion ℚ,
      IsPrimitiveRoot z
        (Nat.card (ResidueField
          ((LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)) - 1) := by
  let := rationalCompletionIntegers_henselian p
  obtain ⟨z, hz⟩ := exists_primitive_tame_root
    (R := (LocalCyclotomic.rationalPlace p).adicCompletionIntegers ℚ)
  exact ⟨z.1, hz.map_of_injective (f := algebraMap _ _) (IsFractionRing.injective _ _)⟩

end LocalRoot
