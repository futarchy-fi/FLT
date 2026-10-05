/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GaloisRepresentation.SerreWeight.NormalizedCharacterExponent
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Character normalization over arbitrary coefficient fields

A character killed by the kernel of a surjective prime-field character is
a power of that character after any field embedding. The normalized exponent
still lies in `1,...,p-1`, independently of the size of the coefficient field.
This is character normalization, not the numerical Serre-weight recipe.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace GaloisRepresentation.SerreWeight
variable {G k : Type*} [Group G] [Field k] {p : ℕ} [Fact p.Prime]
  (f : ZMod p →+* k) (θ : G →* (ZMod p)ˣ) (χ : G →* kˣ)
  (hθ : Function.Surjective θ) (hker : θ.ker ≤ χ.ker)

include hθ hker in
/-- General coefficients introduce no new powers for a prime-field cyclic quotient. -/
theorem exists_coefficient_character_pow :
    ∃ b : ℕ, 1 ≤ b ∧ b ≤ p - 1 ∧ ∀ g,
      χ g = Units.map f.toMonoidHom (θ g) ^ b := by
  have hp : 0 < p - 1 := by have := (Fact.out : p.Prime).two_le; omega
  let : NeZero (p - 1) := ⟨Nat.ne_of_gt hp⟩
  let ψ := θ.liftOfSurjective hθ ⟨χ, hker⟩
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  have hu' : IsPrimitiveRoot (u : ZMod p) (p - 1) := by
    rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hu, Nat.card_eq_fintype_card,
      ZMod.card_units]
  have hv := hu'.map_of_injective f.injective
  have hψ : (ψ u : k) ^ (p - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← map_pow, ZMod.units_pow_card_sub_one_eq_one,
      map_one, Units.val_one]
  obtain ⟨a, ha, hea⟩ := hv.eq_pow_of_pow_eq_one hψ
  have he (g : G) : χ g = Units.map f.toMonoidHom (θ g) ^ a := by
    have hgen : Subgroup.zpowers u = ⊤ := by
      apply Subgroup.eq_top_of_card_eq
      rw [Nat.card_zpowers, hu]
    have hmem : θ g ∈ Subgroup.zpowers u := by rw [hgen]; trivial
    obtain ⟨m, hm⟩ := (Subgroup.mem_zpowers_iff).mp hmem
    apply Units.ext
    have hg : ψ (θ g) = χ g := by simp [ψ]
    rw [← hg, ← hm, map_zpow]
    simp only [Units.val_zpow_eq_zpow_val, Units.val_pow_eq_pow_val,
      Units.coe_map, map_zpow]
    rw [← hea]
    change (f (u : ZMod p) ^ a) ^ m = (f (u : ZMod p) ^ m) ^ a
    simp only [← zpow_natCast, ← zpow_mul, mul_comm]
  by_cases ha0 : a = 0
  · refine ⟨p - 1, hp, le_rfl, fun g ↦ ?_⟩
    rw [he, ha0, pow_zero, ← map_pow, ZMod.units_pow_card_sub_one_eq_one, map_one]
  · exact ⟨a, by omega, by omega, he⟩

/-- A normalized coefficient exponent extracted from the actual character. -/
def coefficientCharacterExponent : ℕ :=
  (exists_coefficient_character_pow f θ χ hθ hker).choose

/-- The normalized exponent has the original prime-field period and recovers the character. -/
theorem coefficientCharacterExponent_spec :
    1 ≤ coefficientCharacterExponent f θ χ hθ hker ∧
      coefficientCharacterExponent f θ χ hθ hker ≤ p - 1 ∧
      ∀ g, χ g = Units.map f.toMonoidHom (θ g) ^
        coefficientCharacterExponent f θ χ hθ hker :=
  (exists_coefficient_character_pow f θ χ hθ hker).choose_spec

include hθ in
/-- The nonzero interval gives uniqueness, independently of any choice of cyclic generator. -/
theorem coefficient_character_exponent_unique {b c : ℕ}
    (hb : 1 ≤ b) (hb' : b ≤ p - 1) (hc : 1 ≤ c) (hc' : c ≤ p - 1)
    (he : ∀ g, Units.map f.toMonoidHom (θ g) ^ b = Units.map f.toMonoidHom (θ g) ^ c) :
    b = c := by
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  obtain ⟨g, hg⟩ := hθ u
  have he' : u ^ b = u ^ c := by
    apply Units.map_injective f.injective
    simpa only [map_pow, hg] using he g
  have hs : u ^ (b - 1) = u ^ (c - 1) := by
    apply mul_right_cancel (b := u)
    simpa only [← pow_succ, Nat.sub_add_cancel hb, Nat.sub_add_cancel hc] using he'
  have ho : orderOf u = p - 1 := by
    simpa only [Nat.card_eq_fintype_card, ZMod.card_units] using hu
  have hh := pow_injOn_Iio_orderOf (by change b - 1 < orderOf u; omega)
    (by change c - 1 < orderOf u; omega) hs
  omega

/-- The cyclotomic character has exponent one over every coefficient field. -/
theorem coefficientCharacterExponent_self
    (h : θ.ker ≤ ((Units.map f.toMonoidHom).comp θ).ker) :
    coefficientCharacterExponent f θ ((Units.map f.toMonoidHom).comp θ) hθ h = 1 := by
  obtain ⟨hb, hb', he⟩ :=
    coefficientCharacterExponent_spec f θ ((Units.map f.toMonoidHom).comp θ) hθ h
  apply coefficient_character_exponent_unique f θ hθ hb hb' le_rfl
    (by have := (Fact.out : p.Prime).two_le; omega)
  intro g
  exact (he g).symm.trans (pow_one _).symm

/-- Enlarging the coefficient field preserves the uniquely normalized exponent. -/
theorem coefficientCharacterExponent_map {l : Type*} [Field l] (e : k →+* l)
    (h : θ.ker ≤ ((Units.map e.toMonoidHom).comp χ).ker) :
    coefficientCharacterExponent (e.comp f) θ ((Units.map e.toMonoidHom).comp χ) hθ h =
      coefficientCharacterExponent f θ χ hθ hker := by
  obtain ⟨hb, hb', he⟩ := coefficientCharacterExponent_spec (e.comp f) θ
    ((Units.map e.toMonoidHom).comp χ) hθ h
  obtain ⟨hc, hc', hf⟩ := coefficientCharacterExponent_spec f θ χ hθ hker
  apply coefficient_character_exponent_unique (e.comp f) θ hθ hb hb' hc hc'
  intro g
  rw [← he g]
  have hh := congrArg (Units.map e.toMonoidHom) (hf g)
  have hm : Units.map (e.comp f).toMonoidHom (θ g) =
      Units.map e.toMonoidHom (Units.map f.toMonoidHom (θ g)) := by
    apply Units.ext
    rfl
  rw [hm]
  exact hh.trans (map_pow _ _ _)

end GaloisRepresentation.SerreWeight
