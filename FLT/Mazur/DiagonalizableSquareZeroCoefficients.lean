/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DiagonalizableCobarAlgebra
public import Mathlib.RingTheory.Ideal.Quotient.Defs

/-!
# Square-zero ideals in diagonalizable coordinates

Functions with coefficients in a square-zero base ideal multiply to zero in
every character algebra. Character substitution and the integral contraction
preserve that ideal. Thus corrections remain in the original infinitesimal
kernel, rather than changing the prescribed reduction.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.DiagonalizableCobar

variable {R G H : Type*} [CommRing R] [AddCommMonoid G] [AddCommMonoid H]
  (I : Ideal R)

/-- Coefficients lie in the given base ideal, with no reducedness condition. -/
def InCoefficients (p : AddMonoidAlgebra R G) : Prop := ∀ a, p.coeff a ∈ I

/-- Coefficient containment is precisely vanishing on the original quotient base. -/
theorem inCoefficients_iff_reduction (p : AddMonoidAlgebra R G) :
    InCoefficients I p ↔ AddMonoidAlgebra.mapRingHom G (Ideal.Quotient.mk I) p = 0 := by
  constructor
  · intro h
    ext a
    exact (Ideal.Quotient.eq_zero_iff_mem).mpr (h a)
  · intro h a
    have ha := congrArg (fun q : AddMonoidAlgebra (R ⧸ I) G ↦ q.coeff a) h
    exact (Ideal.Quotient.eq_zero_iff_mem).mp ha

/-- All actual character substitutions preserve the infinitesimal coefficient ideal. -/
theorem InCoefficients.mapDomain {p : AddMonoidAlgebra R G} (hp : InCoefficients I p)
    (f : G →+ H) : InCoefficients I (AddMonoidAlgebra.mapDomainAlgHom R R f p) := by
  classical
  intro b
  change Finsupp.mapDomain f p.coeff b ∈ I
  rw [Finsupp.mapDomain_apply, Finsupp.sum]
  apply I.sum_mem
  intro a ha
  by_cases h : f a = b <;> simp [h, hp a]

/-- The explicit correction keeps every coefficient in the original ideal. -/
theorem InCoefficients.correction {p : AddMonoidAlgebra R (G × G)}
    (hp : InCoefficients I p) : InCoefficients I (correction R G p) :=
  fun a ↦ hp (a, 0)

/-- Two functions in a square-zero coefficient ideal have exactly zero product. -/
theorem InCoefficients.mul_eq_zero (hI : I ^ 2 = ⊥)
    {p q : AddMonoidAlgebra R G} (hp : InCoefficients I p) (hq : InCoefficients I q) :
    p * q = 0 := by
  classical
  have hm (a b : G) : p.coeff a * q.coeff b = 0 := by
    have h : p.coeff a * q.coeff b ∈ I ^ 2 := by
      simpa only [pow_two] using Ideal.mul_mem_mul (hp a) (hq b)
    simpa only [hI, Ideal.mem_bot] using h
  ext c
  simp [AddMonoidAlgebra.coeff_mul, Finsupp.sum, hm]

/-- A correction in the original square-zero ideal is itself square zero. -/
theorem correction_sq_zero (hI : I ^ 2 = ⊥) {p : AddMonoidAlgebra R (G × G)}
    (hp : InCoefficients I p) : correction R G p * correction R G p = 0 :=
  (hp.correction I).mul_eq_zero I hI (hp.correction I)

end FLT.Mazur.DiagonalizableCobar
