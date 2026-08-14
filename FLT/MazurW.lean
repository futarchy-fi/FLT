module

public import Mathlib.GroupTheory.Torsion
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point

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
  sorry

theorem mazur_W_nonvacuity_full_two_torsion :
    ∃ (E : WeierstrassCurve ℚ) (hE : E.IsElliptic),
      letI : E.IsElliptic := hE
      ∃ f : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point,
        Function.Injective f := by
  let E : WeierstrassCurve ℚ := ⟨0, 0, 0, -1, 0⟩
  have hE : E.IsElliptic := by
    refine ⟨?_⟩
    have hΔ : E.Δ = (64 : ℚ) := by
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
  have hQ : (E⁄ℚ).Nonsingular 1 0 := by
    apply (WeierstrassCurve.Affine.equation_iff_nonsingular
      (W := E⁄ℚ)).mp
    rw [WeierstrassCurve.Affine.equation_iff]
    norm_num [E, WeierstrassCurve.baseChange, WeierstrassCurve.map]

  let P : (E⁄ℚ).Point := .some 0 0 hP
  let Q : (E⁄ℚ).Point := .some 1 0 hQ

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
    have hx : (0 : ℚ) = 1 := by
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
