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

/-- Cartography node A4/W non-vacuity fixture: some elliptic curve over `ℚ`
has full rational `2`-torsion.  For `FreyPackage.mazur` (A5), the generic
existence statement is replaced by A4's curve-specific survival result before
applying `mazur_W`. -/
theorem mazur_W_nonvacuity_full_two_torsion :
    ∃ (E : WeierstrassCurve ℚ) (hE : E.IsElliptic),
      letI : E.IsElliptic := hE
      ∃ f : (ZMod 2 × ZMod 2) →+ (E⁄ℚ).Point,
        Function.Injective f := by
  sorry
