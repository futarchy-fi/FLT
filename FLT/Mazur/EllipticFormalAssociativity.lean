/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticFormalFieldPoint
public import FLT.Mazur.EllipticFormalGenericParameters
public import Mathlib.RingTheory.Localization.FractionRing

/-!
# Associativity of elliptic formal addition over domains

Embed the ring of series in three variables in its fraction field. The four
secants occurring in associativity have distinct endpoints. Their point sums
are associative in Mathlib's projective group, and injectivity of the formal
parameter brings that equality back to the integral series ring.
-/

@[expose] public section

namespace FLT.Mazur.FormalInfinity
open MvPowerSeries

variable {R : Type*} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

/-- Associativity at three independent formal variables over a domain. -/
theorem add_assoc_variables_of_domain :
    add W (add W (X 0) (X 1)) (X 2) =
      add W (X 0) (add W (X 1) (X 2)) (σ := Fin 3) := by
  let A := MvPowerSeries (Fin 3) R
  let K := FractionRing A
  let f : A →+* K := algebraMap A K
  have hf : Function.Injective f := IsFractionRing.injective A K
  have h0 : (X (0 : Fin 3) : A).constantCoeff = 0 := by simp
  have h1 : (X (1 : Fin 3) : A).constantCoeff = 0 := by simp
  have h2 : (X (2 : Fin 3) : A).constantCoeff = 0 := by simp
  have h01 : (X (0 : Fin 3) : A) ≠ X 1 := by simp [X_inj]
  have h12 : (X (1 : Fin 3) : A) ≠ X 2 := by simp [X_inj]
  have hl : add W (X (0 : Fin 3)) (X 1) ≠ (X 2 : A) :=
    add_X_X_ne_X W (by decide) (by decide)
  have hr : (X (0 : Fin 3) : A) ≠ add W (X 1) (X 2) :=
    (add_X_X_ne_X W (by decide) (by decide)).symm
  apply (fieldPoint_eq_iff W f hf
    (constantCoeff_add W (constantCoeff_add W h0 h1) h2)
    (constantCoeff_add W h0 (constantCoeff_add W h1 h2))).mp
  rw [fieldPoint_add_of_ne W f hf (constantCoeff_add W h0 h1) h2 hl,
    fieldPoint_add_of_ne W f hf h0 (constantCoeff_add W h1 h2) hr,
    fieldPoint_add_of_ne W f hf h0 h1 h01, fieldPoint_add_of_ne W f hf h1 h2 h12]
  exact _root_.add_assoc _ _ _

end FLT.Mazur.FormalInfinity
