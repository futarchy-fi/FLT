/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.FiniteHomologyCard

/-!
# Cardinal arithmetic for a six-term exact cycle

Count each module as incoming image times outgoing image. Multiplying the
three alternate equalities gives the alternating cardinal identity.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open CategoryTheory

variable {k : Type} [CommRing k]

/-- Exactness expresses the middle cardinality as the two adjacent image cardinalities. -/
theorem exact_card_eq_range_mul_range (S : ShortComplex (ModuleCat k)) (hS : S.Exact) :
    Nat.card S.X₂ = Nat.card S.f.hom.range * Nat.card S.g.hom.range := by
  rw [linearMap_card_eq_ker_mul_range S.g.hom, ← hS.moduleCat_range_eq_ker]

/-- The alternating cardinal identity for a six-term exact cycle. -/
theorem sixTerm_card {A B C D E F : ModuleCat k}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D)
    (d : D ⟶ E) (e : E ⟶ F) (f : F ⟶ A)
    (hab : a ≫ b = 0) (hbc : b ≫ c = 0) (hcd : c ≫ d = 0)
    (hde : d ≫ e = 0) (hef : e ≫ f = 0) (hfa : f ≫ a = 0)
    (hB : (ShortComplex.mk a b hab).Exact) (hC : (ShortComplex.mk b c hbc).Exact)
    (hD : (ShortComplex.mk c d hcd).Exact) (hE : (ShortComplex.mk d e hde).Exact)
    (hF : (ShortComplex.mk e f hef).Exact) (hA : (ShortComplex.mk f a hfa).Exact) :
    Nat.card A * Nat.card C * Nat.card E = Nat.card B * Nat.card D * Nat.card F := by
  rw [exact_card_eq_range_mul_range _ hA, exact_card_eq_range_mul_range _ hB,
    exact_card_eq_range_mul_range _ hC, exact_card_eq_range_mul_range _ hD,
    exact_card_eq_range_mul_range _ hE, exact_card_eq_range_mul_range _ hF]
  ring

/-- For finite nonempty terms, the six-term identity gives multiplicativity of ratios. -/
theorem sixTerm_ratio {a b c d e f : ℕ} (ha : 0 < a) (hc : 0 < c) (he : 0 < e)
    (h : a * c * e = b * d * f) :
    (b : ℚ) / e = (a : ℚ) / d * ((c : ℚ) / f) := by
  have hp : 0 < b * d * f := h ▸ Nat.mul_pos (Nat.mul_pos ha hc) he
  have hd : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left
    (Nat.pos_of_mul_pos_right hp)).ne'
  have hf : (f : ℚ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mul_pos_left hp).ne'
  have he' : (e : ℚ) ≠ 0 := by exact_mod_cast he.ne'
  have h' : (a : ℚ) * c * e = (b : ℚ) * d * f := by exact_mod_cast h
  rw [div_mul_div_comm, div_eq_div_iff he' (mul_ne_zero hd hf)]
  simpa only [mul_assoc] using h'.symm

end LocalClassFieldTheory
