/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.RaynaudCoordinateGeneration
public import Mathlib.Data.Nat.Periodic
public import Mathlib.Algebra.MvPolynomial.Eval

/-!
# A finite cycle of actual coordinate generators

Frobenius periodicity restricts the already proved generation theorem to
one finite cycle. Its cyclic coefficients and coordinate rank are derived
from the actual model.
-/

@[expose] public noncomputable section
namespace ThreeAdicPlan
open IsLocalRing

variable {R K F : Type} [CommRing R] [IsDomain R] [IsPrincipalIdealRing R]
  [HenselianLocalRing R] [IsSepClosed (ResidueField R)] [Field K] [Algebra R K]
  [CharZero K] [IsFractionRing R K] [Field F] [Fintype F] [DecidableEq F]
  [Invertible (Fintype.card Fˣ : R)] (X : FF R K) [Module F X.Points]
  (lift : F → ModelHom X X) (h0 : lift 0 = ModelHom.zero X X)
  (h1 : lift 1 = BialgHom.id R X.CoordinateRing)
  (hmul : ∀ a b, lift (a * b) = (lift b).comp (lift a))
  (hadd : ∀ a b, lift (a + b) = (lift a).add (lift b))
  (p : ℕ) [CharP F p] [CharP (ResidueField R) p]
  (hdim : Module.finrank F X.Points = 1)
  (hlift : ∀ a x, genericHom (lift a) x = a • x) (e : F →+* ResidueField R)
  (r : ℕ+) (hr : Fintype.card F = p ^ (r : ℕ))

include hr in
omit [Invertible (Fintype.card Fˣ : R)] in
/-- Reduction of the coordinate index modulo the actual Frobenius period. -/
theorem FF.fundamentalCoordinate_mod (i : ℕ) :
    X.fundamentalCoordinate p lift h1 hmul hdim hlift e (i % r) =
      X.fundamentalCoordinate p lift h1 hmul hdim hlift e i := by
  have hper : Function.Periodic
      (X.fundamentalCoordinate p lift h1 hmul hdim hlift e) (r : ℕ) :=
    X.fundamentalCoordinate_periodic p lift h1 hmul hdim hlift e r hr
  exact hper.map_mod_nat i

include h0 hadd hr in
/-- One finite Frobenius cycle generates the actual integral coordinate algebra. -/
theorem FF.finite_fundamental_adjoin_eq_top :
    Algebra.adjoin R (Set.range (fun i : Fin r ↦
      X.fundamentalCoordinate p lift h1 hmul hdim hlift e i)) = ⊤ := by
  apply top_unique
  rw [← X.fundamental_adjoin_eq_top lift h0 h1 hmul hadd p hdim hlift e]
  apply Algebra.adjoin_le
  rintro _ ⟨i, rfl⟩
  apply Algebra.subset_adjoin
  exact ⟨⟨i % r, Nat.mod_lt i r.pos⟩,
    X.fundamentalCoordinate_mod lift h1 hmul p hdim hlift e r hr i⟩

include h0 hadd hr in
/-- Polynomial evaluation at one cycle is surjective over the integral base. -/
theorem FF.fundamental_aeval_surjective :
    Function.Surjective (MvPolynomial.aeval (R := R) (fun i : Fin r ↦
      X.fundamentalCoordinate p lift h1 hmul hdim hlift e i)) := by
  rw [← AlgHom.range_eq_top, ← Algebra.adjoin_range_eq_range_aeval]
  exact X.finite_fundamental_adjoin_eq_top lift h0 h1 hmul hadd p hdim hlift e r hr

include hr in
omit [Invertible (Fintype.card Fˣ : R)] in
/-- The finite cycle has actual integral cyclic power coefficients. -/
theorem FF.exists_finite_fundamental_relations :
    ∃ a : Fin r → R, ∀ i : Fin r,
      X.fundamentalCoordinate p lift h1 hmul hdim hlift e i ^ p =
        a i • X.fundamentalCoordinate p lift h1 hmul hdim hlift e
          ((i.val + 1) % r) := by
  choose a ha using fun i : Fin r ↦
    X.fundamentalCoordinate_power p lift h1 hmul hdim hlift e i
  refine ⟨a, fun i ↦ ?_⟩
  rw [X.fundamentalCoordinate_mod lift h1 hmul p hdim hlift e r hr]
  exact ha i

include hdim hr in
omit [DecidableEq F] [Invertible (Fintype.card Fˣ : R)] [IsDomain R]
  [IsPrincipalIdealRing R] [IsSepClosed (ResidueField R)] [IsFractionRing R K]
  [CharP F p] [CharP (ResidueField R) p] in
/-- The coordinate rank is exactly p to the length of the Frobenius cycle. -/
theorem FF.fundamental_coordinate_finrank : Module.finrank R X.CoordinateRing = p ^ (r : ℕ) := by
  rw [X.coordinate_finrank,
    ← Nat.card_congr (Module.nonempty_linearEquiv_of_finrank_eq_one hdim).some.toEquiv,
    Nat.card_eq_fintype_card, hr]

end ThreeAdicPlan
