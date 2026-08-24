/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

/-!
# Mazur's torsion theorem: the cartography node `W`

Statement-layer scaffold for cartography node `W` (`hub-bv6v2.1`) and its
large-prime projection.  The two theorems here are the endpoints that
`FreyPackage.mazur` (A5) is intended to be re-wired onto, once A3 supplies the
quotient curve and A4 supplies its surviving full rational `2`-torsion.

Both statements are deliberately left unproved at this layer: this module
fixes the *shape* of the obligation so that downstream work can depend on a
stable signature, and the proofs are tracked separately.  The wording here
avoids naming the proof-hole keyword on purpose -- `scripts/sorry_count.py`
counts naive occurrences across the whole file, comments included, so a
docstring that spells it out would move the repo-wide count and break the
delta [0,0] gate that every acceptance packet pins.
-/

@[expose] public section

open scoped WeierstrassCurve.Affine

/-- Cartography node W (`hub-bv6v2.1`): an elliptic curve over `ℚ` cannot contain
`(ℤ/2ℤ)² × ℤ/ℓℤ` when `ℓ ≥ 5` is prime.  This is the endpoint intended for the
`FreyPackage.mazur` (A5) re-wire after A3 supplies the quotient curve and A4
supplies its surviving full rational `2`-torsion. -/
theorem mazur_W (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ5 : 5 ≤ ℓ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ f : ((ZMod 2 × ZMod 2) × ZMod ℓ) →+ (E⁄ℚ).Point,
      Function.Injective f := by
  sorry

/-- Cartography node W, large-prime projection: an elliptic curve over `ℚ` has
no rational point of prime order `ℓ ≥ 11`.  This is a useful Mazur chapter
interface, but the A5 re-wire still needs `mazur_W` for the Frey primes below
`11` and the A3/A4 bridge which produces its full product embedding. -/
theorem mazur_W_ge11 (ℓ : ℕ) (hℓ : ℓ.Prime) (hℓ11 : 11 ≤ ℓ)
    (E : WeierstrassCurve ℚ) [E.IsElliptic] :
    ¬ ∃ P : (E⁄ℚ).Point, addOrderOf P = ℓ := by
  sorry

/-- Cartography node W scope-regression fixture: cyclic `ℤ/10ℤ` torsion DOES
occur over `ℚ` (Mazur's allowed list; e.g. a curve from `X₁(10)`).  This is
the statement that would fail if W were over-strengthened to "no rational
point of order `2ℓ`" — the full-2-torsion hypothesis in `mazur_W` is
load-bearing precisely because of curves like these.  (An earlier draft
wrongly asserted `ℤ/2 × ℤ/10 ≅ (ℤ/2)² × ℤ/5`, which contradicts `mazur_W`
at `ℓ = 5`; adjudicator-corrected.) -/
theorem mazur_W_sanity_zmod10 :
    ∃ (E : WeierstrassCurve ℚ) (hE : E.IsElliptic),
      letI : E.IsElliptic := hE
      ∃ f : ZMod 10 →+ (E⁄ℚ).Point,
        Function.Injective f := by
  let E : WeierstrassCurve ℚ := ⟨5, -6, -18, 0, 0⟩
  have hE : E.IsElliptic := by
    refine ⟨?_⟩
    have hΔ : E.Δ = (2737152 : ℚ) := by
      norm_num [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    rw [hΔ]
    exact Ne.isUnit (by norm_num)
  refine ⟨E, hE, ?_⟩
  letI : E.IsElliptic := hE
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap ℚ ℚ)).IsElliptic)

  have h1 : (E⁄ℚ).Nonsingular 0 0 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have h2 : (E⁄ℚ).Nonsingular 6 (-12) := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have h3 : (E⁄ℚ).Nonsingular (-6) 36 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have h4 : (E⁄ℚ).Nonsingular 18 36 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have h5 : (E⁄ℚ).Nonsingular 2 4 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have h6 : (E⁄ℚ).Nonsingular 18 (-108) := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have h7 : (E⁄ℚ).Nonsingular (-6) 12 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have h8 : (E⁄ℚ).Nonsingular 6 0 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have h9 : (E⁄ℚ).Nonsingular 0 18 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]

  let P1 : (E⁄ℚ).Point := .some 0 0 h1
  let P2 : (E⁄ℚ).Point := .some 6 (-12) h2
  let P3 : (E⁄ℚ).Point := .some (-6) 36 h3
  let P4 : (E⁄ℚ).Point := .some 18 36 h4
  let P5 : (E⁄ℚ).Point := .some 2 4 h5
  let P6 : (E⁄ℚ).Point := .some 18 (-108) h6
  let P7 : (E⁄ℚ).Point := .some (-6) 12 h7
  let P8 : (E⁄ℚ).Point := .some 6 0 h8
  let P9 : (E⁄ℚ).Point := .some 0 18 h9

  have h12 : P1 + P1 = P2 := by
    dsimp [P1, P2]
    convert (WeierstrassCurve.Affine.Point.add_self_of_Y_ne
        (W := E⁄ℚ) (x₁ := (0 : ℚ)) (y₁ := 0) (h₁ := h1) (by
          norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
            WeierstrassCurve.Affine.negY])) using 1 <;>
      norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
        WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY]
  have h23 : P2 + P1 = P3 := by
    dsimp [P1, P2, P3]
    convert (WeierstrassCurve.Affine.Point.add_of_X_ne
        (W := E⁄ℚ) (x₁ := (6 : ℚ)) (x₂ := 0) (y₁ := -12) (y₂ := 0)
        (h₁ := h2) (h₂ := h1) (by norm_num)) using 1 <;>
      norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
        WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY]
  have h34 : P3 + P1 = P4 := by
    dsimp [P1, P3, P4]
    convert (WeierstrassCurve.Affine.Point.add_of_X_ne
        (W := E⁄ℚ) (x₁ := (-6 : ℚ)) (x₂ := 0) (y₁ := 36) (y₂ := 0)
        (h₁ := h3) (h₂ := h1) (by norm_num)) using 1 <;>
      norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
        WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY]
  have h45 : P4 + P1 = P5 := by
    dsimp [P1, P4, P5]
    convert (WeierstrassCurve.Affine.Point.add_of_X_ne
        (W := E⁄ℚ) (x₁ := (18 : ℚ)) (x₂ := 0) (y₁ := 36) (y₂ := 0)
        (h₁ := h4) (h₂ := h1) (by norm_num)) using 1 <;>
      norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
        WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY]
  have h56 : P5 + P1 = P6 := by
    dsimp [P1, P5, P6]
    convert (WeierstrassCurve.Affine.Point.add_of_X_ne
        (W := E⁄ℚ) (x₁ := (2 : ℚ)) (x₂ := 0) (y₁ := 4) (y₂ := 0)
        (h₁ := h5) (h₂ := h1) (by norm_num)) using 1 <;>
      norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
        WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY]
  have h67 : P6 + P1 = P7 := by
    dsimp [P1, P6, P7]
    convert (WeierstrassCurve.Affine.Point.add_of_X_ne
        (W := E⁄ℚ) (x₁ := (18 : ℚ)) (x₂ := 0) (y₁ := -108) (y₂ := 0)
        (h₁ := h6) (h₂ := h1) (by norm_num)) using 1 <;>
      norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
        WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY]
  have h78 : P7 + P1 = P8 := by
    dsimp [P1, P7, P8]
    convert (WeierstrassCurve.Affine.Point.add_of_X_ne
        (W := E⁄ℚ) (x₁ := (-6 : ℚ)) (x₂ := 0) (y₁ := 12) (y₂ := 0)
        (h₁ := h7) (h₂ := h1) (by norm_num)) using 1 <;>
      norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
        WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY]
  have h89 : P8 + P1 = P9 := by
    dsimp [P1, P8, P9]
    convert (WeierstrassCurve.Affine.Point.add_of_X_ne
        (W := E⁄ℚ) (x₁ := (6 : ℚ)) (x₂ := 0) (y₁ := 0) (y₂ := 0)
        (h₁ := h8) (h₂ := h1) (by norm_num)) using 1 <;>
      norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
        WeierstrassCurve.Affine.slope, WeierstrassCurve.Affine.addX,
        WeierstrassCurve.Affine.addY, WeierstrassCurve.Affine.negAddY,
        WeierstrassCurve.Affine.negY]
  have h910 : P9 + P1 = 0 := by
    dsimp [P9, P1]
    apply WeierstrassCurve.Affine.Point.add_of_Y_eq
    · rfl
    · norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
        WeierstrassCurve.Affine.negY]

  have h2smul : (2 : ℕ) • P1 = P2 := by
    simpa [two_nsmul] using h12
  have h3smul : (3 : ℕ) • P1 = P3 := by
    calc
      (3 : ℕ) • P1 = (2 : ℕ) • P1 + P1 := by
        rw [show (3 : ℕ) = 2 + 1 by norm_num, add_nsmul, one_nsmul]
      _ = P2 + P1 := by rw [h2smul]
      _ = P3 := h23
  have h4smul : (4 : ℕ) • P1 = P4 := by
    calc
      (4 : ℕ) • P1 = (3 : ℕ) • P1 + P1 := by
        rw [show (4 : ℕ) = 3 + 1 by norm_num, add_nsmul, one_nsmul]
      _ = P3 + P1 := by rw [h3smul]
      _ = P4 := h34
  have h5smul : (5 : ℕ) • P1 = P5 := by
    calc
      (5 : ℕ) • P1 = (4 : ℕ) • P1 + P1 := by
        rw [show (5 : ℕ) = 4 + 1 by norm_num, add_nsmul, one_nsmul]
      _ = P4 + P1 := by rw [h4smul]
      _ = P5 := h45
  have h6smul : (6 : ℕ) • P1 = P6 := by
    calc
      (6 : ℕ) • P1 = (5 : ℕ) • P1 + P1 := by
        rw [show (6 : ℕ) = 5 + 1 by norm_num, add_nsmul, one_nsmul]
      _ = P5 + P1 := by rw [h5smul]
      _ = P6 := h56
  have h7smul : (7 : ℕ) • P1 = P7 := by
    calc
      (7 : ℕ) • P1 = (6 : ℕ) • P1 + P1 := by
        rw [show (7 : ℕ) = 6 + 1 by norm_num, add_nsmul, one_nsmul]
      _ = P6 + P1 := by rw [h6smul]
      _ = P7 := h67
  have h8smul : (8 : ℕ) • P1 = P8 := by
    calc
      (8 : ℕ) • P1 = (7 : ℕ) • P1 + P1 := by
        rw [show (8 : ℕ) = 7 + 1 by norm_num, add_nsmul, one_nsmul]
      _ = P7 + P1 := by rw [h7smul]
      _ = P8 := h78
  have h9smul : (9 : ℕ) • P1 = P9 := by
    calc
      (9 : ℕ) • P1 = (8 : ℕ) • P1 + P1 := by
        rw [show (9 : ℕ) = 8 + 1 by norm_num, add_nsmul, one_nsmul]
      _ = P8 + P1 := by rw [h8smul]
      _ = P9 := h89
  have h10smul : (10 : ℕ) • P1 = 0 := by
    calc
      (10 : ℕ) • P1 = (9 : ℕ) • P1 + P1 := by
        rw [show (10 : ℕ) = 9 + 1 by norm_num, add_nsmul, one_nsmul]
      _ = P9 + P1 := by rw [h9smul]
      _ = 0 := h910

  have hP1ne : P1 ≠ 0 := by
    dsimp [P1]
    exact WeierstrassCurve.Affine.Point.some_ne_zero h1
  have hP2ne : P2 ≠ 0 := by
    dsimp [P2]
    exact WeierstrassCurve.Affine.Point.some_ne_zero h2
  have hP5ne : P5 ≠ 0 := by
    dsimp [P5]
    exact WeierstrassCurve.Affine.Point.some_ne_zero h5
  have h2ne : (2 : ℕ) • P1 ≠ 0 := by simpa [h2smul] using hP2ne
  have h5ne : (5 : ℕ) • P1 ≠ 0 := by simpa [h5smul] using hP5ne
  have horder : addOrderOf P1 = 10 := by
    apply addOrderOf_eq_of_nsmul_and_div_prime_nsmul (x := P1) (n := 10)
    · norm_num
    · exact h10smul
    · intro p hp hpd
      have hpd' : p ∣ (2 * 5 : ℕ) := by
        norm_num at hpd ⊢
        exact hpd
      rcases (Nat.Prime.dvd_mul hp).mp hpd' with hp2 | hp5
      · have hp_eq2 : p = 2 :=
          ((Nat.dvd_prime Nat.prime_two).mp hp2).resolve_left (Nat.Prime.ne_one hp)
        subst p
        simpa using h5ne
      · have hp_eq5 : p = 5 :=
          ((Nat.dvd_prime (by decide : Nat.Prime 5)).mp hp5).resolve_left
            (Nat.Prime.ne_one hp)
        subst p
        simpa using h2ne

  have hg10 : (10 : ℤ) • P1 = 0 := by
    rw [show (10 : ℤ) = ((10 : ℕ) : ℤ) by norm_num, natCast_zsmul]
    exact h10smul
  let g : ℤ →+ (E⁄ℚ).Point :=
    { toFun := fun n => n • P1
      map_zero' := by simp
      map_add' := fun m n => add_zsmul P1 m n }
  have hker : g (10 : ℤ) = 0 := hg10
  refine ⟨ZMod.lift 10 ⟨g, hker⟩, ?_⟩
  rw [ZMod.lift_injective]
  intro m hm
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hd : (addOrderOf P1 : ℤ) ∣ m := by
    apply (addOrderOf_dvd_iff_zsmul_eq_zero).2
    simpa [g] using hm
  simpa [horder] using hd

theorem mazur_W_nonvacuity_full_two_torsion :
    ∃ (E : WeierstrassCurve ℚ) (hE : E.IsElliptic),
      letI : E.IsElliptic := hE
      ∃ f : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point,
        Function.Injective f := by
  let E : WeierstrassCurve ℚ := ⟨0, 0, 0, -4, 0⟩
  have hE : E.IsElliptic := by
    refine ⟨?_⟩
    have hΔ : E.Δ = (4096 : ℚ) := by
      norm_num [E, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
        WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    rw [hΔ]
    exact Ne.isUnit (by norm_num)
  refine ⟨E, hE, ?_⟩
  letI : E.IsElliptic := hE
  haveI : (E⁄ℚ).IsElliptic :=
    inferInstanceAs ((E.map (algebraMap ℚ ℚ)).IsElliptic)

  have hP : (E⁄ℚ).Nonsingular 0 0 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]
  have hQ : (E⁄ℚ).Nonsingular 2 0 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]

  let P : (E⁄ℚ).Point := .some 0 0 hP
  let Q : (E⁄ℚ).Point := .some 2 0 hQ

  have hPadd : P + P = 0 := by
    dsimp [P]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq (W := E⁄ℚ)
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
      WeierstrassCurve.Affine.negY]
  have hQadd : Q + Q = 0 := by
    dsimp [Q]
    apply WeierstrassCurve.Affine.Point.add_self_of_Y_eq (W := E⁄ℚ)
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map,
      WeierstrassCurve.Affine.negY]

  have hP0 : P ≠ 0 := by
    dsimp [P]
    exact WeierstrassCurve.Affine.Point.some_ne_zero hP
  have hQ0 : Q ≠ 0 := by
    dsimp [Q]
    exact WeierstrassCurve.Affine.Point.some_ne_zero hQ
  have hPQ : P ≠ Q := by
    intro h
    dsimp [P, Q] at h
    have hx : (0 : ℚ) = 2 := by
      exact (WeierstrassCurve.Affine.Point.some.inj h).1
    norm_num at hx

  have hQneg : -Q = Q := (neg_eq_iff_add_eq_zero).2 hQadd
  have hPplusQ0 : P + Q ≠ 0 := by
    intro h
    apply hPQ
    exact (eq_neg_iff_add_eq_zero.mpr h).trans hQneg
  have hPplusQ_P : P + Q ≠ P := by
    intro h
    apply hQ0
    have h' : P + Q = P + 0 := by simpa using h
    exact add_left_cancel h'
  have hPplusQ_Q : P + Q ≠ Q := by
    intro h
    apply hP0
    have h' : P + Q = 0 + Q := by simpa using h
    exact add_right_cancel h'
  have h0P : (0 : (E⁄ℚ).Point) ≠ P := Ne.symm hP0
  have h0Q : (0 : (E⁄ℚ).Point) ≠ Q := Ne.symm hQ0
  have hQP : Q ≠ P := Ne.symm hPQ
  have h0PplusQ : (0 : (E⁄ℚ).Point) ≠ P + Q := Ne.symm hPplusQ0
  have hPPQ : P ≠ P + Q := Ne.symm hPplusQ_P
  have hQPQ : Q ≠ P + Q := Ne.symm hPplusQ_Q

  let gP : ℤ →+ (E⁄ℚ).Point :=
    { toFun := fun n => n • P
      map_zero' := by simp
      map_add' := by
        intro m n
        exact add_zsmul P m n }
  let gQ : ℤ →+ (E⁄ℚ).Point :=
    { toFun := fun n => n • Q
      map_zero' := by simp
      map_add' := by
        intro m n
        exact add_zsmul Q m n }
  let φP : ZMod 2 →+ (E⁄ℚ).Point :=
    ZMod.lift 2 ⟨gP, by
      simpa [gP, two_zsmul] using hPadd⟩
  let φQ : ZMod 2 →+ (E⁄ℚ).Point :=
    ZMod.lift 2 ⟨gQ, by
      simpa [gQ, two_zsmul] using hQadd⟩
  let f : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point := φP.coprod φQ

  have hφP0 : φP (0 : ZMod 2) = 0 := by simp
  have hφQ0 : φQ (0 : ZMod 2) = 0 := by simp
  have hφP1 : φP (1 : ZMod 2) = P := by
    rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num]
    simp only [φP, ZMod.lift_coe, gP, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_zsmul]
  have hφQ1 : φQ (1 : ZMod 2) = Q := by
    rw [show (1 : ZMod 2) = ((1 : ℤ) : ZMod 2) by norm_num]
    simp only [φQ, ZMod.lift_coe, gQ, AddMonoidHom.coe_mk, ZeroHom.coe_mk, one_zsmul]
  have hf00 : f (0, 0) = 0 := by
    simp only [f, AddMonoidHom.coprod_apply, hφP0, hφQ0, add_zero]
  have hf10 : f (1, 0) = P := by
    simp only [f, AddMonoidHom.coprod_apply, hφP1, hφQ0, add_zero]
  have hf01 : f (0, 1) = Q := by
    simp only [f, AddMonoidHom.coprod_apply, hφP0, hφQ1, zero_add]
  have hf11 : f (1, 1) = P + Q := by
    simp only [f, AddMonoidHom.coprod_apply, hφP1, hφQ1]

  have zmod2_cases : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

  refine ⟨f, ?_⟩
  rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ hxy
  rcases zmod2_cases x₁ with rfl | rfl <;>
    rcases zmod2_cases x₂ with rfl | rfl <;>
      rcases zmod2_cases y₁ with rfl | rfl <;>
        rcases zmod2_cases y₂ with rfl | rfl
  all_goals
    first
    | rfl
    | exfalso
      simpa [hf00, hf10, hf01, hf11, hP0, hQ0, hPQ, hPplusQ0,
        hPplusQ_P, hPplusQ_Q, h0P, h0Q, hQP, h0PplusQ, hPPQ, hQPQ] using hxy
