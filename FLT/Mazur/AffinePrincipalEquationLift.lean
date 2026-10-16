/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenDenominators

/-!
# Lift an original basic-open equation through a principal-power kernel

A local equation lifts to divisibility by the kernel generator after multiplying
by a power of the lifted denominator. The two powers have separate roles;
neither is cancelled, and the section ring need not be reduced.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AffinePrincipalEquationLift
variable {X : Scheme} {A : Type*} [CommRing A] (U : X.affineOpens)
variable (π : A →+* Γ(X, U.1)) (t : A) (N : ℕ)
variable (hπ : RingHom.ker π = Ideal.span {t ^ N})
variable (d : Γ(X, ⊤)) (hd : X.basicOpen d ≤ U.1)
variable (d' : A) (hd' : π d' = X.presheaf.map (homOfLE le_top).op d)
include hπ hd'

/-- A basic-open equation lifts exactly to denominator-power principal divisibility. -/
theorem equation_iff (z : A) :
    X.presheaf.map (homOfLE hd).op (π z) = 0 ↔
      ∃ r : ℕ, t ^ N ∣ d' ^ r * z := by
  have he : X.basicOpen d =
      X.basicOpen (X.presheaf.map (homOfLE (show U.1 ≤ ⊤ from le_top)).op d) := by
    rw [Scheme.basicOpen_res, inf_eq_right.mpr hd]
  rw [AffineOpenDenominators.zero_iff U.2 _ he]
  have hk (a : A) : π a = 0 ↔ t ^ N ∣ a := by
    change a ∈ RingHom.ker π ↔ _
    rw [hπ, Ideal.mem_span_singleton]
  apply exists_congr
  intro r
  rw [← hk, map_mul, map_pow, hd']

end FLT.Mazur.AffinePrincipalEquationLift
