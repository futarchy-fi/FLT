/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationTangentRootNaturality
public import FLT.Mazur.WeierstrassDilatationTangentCorrection

/-!
# Coefficient naturality of the full terminal inverse and product correction

The inverse polynomial is compared by its unique defining equation.
The complete product correction keeps the original constant and linear terms.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (W : WeierstrassCurve R) (r : R[X]) (I : Ideal R) (hI : IsNilpotent I)
  (J : Ideal S) (hJ : IsNilpotent J) (hf : I ≤ J.comap f)
  (hrI : r ∈ I.map C) (ha : IsUnit W.a₁)
local notation "hrJ" => terminalPolynomialIdeal_map f I J hf hrI

/-- Restriction preserves the entire inverse polynomial, including every nilpotent correction. -/
theorem terminalInversePolynomial_map :
    (terminalInversePolynomial W r I hI hrI ha).map f =
      terminalInversePolynomial (W.map f) (r.map f) J hJ hrJ (ha.map f) := by
  apply terminalInverseX_unique (W.map f) 0 (r.map f) J hJ hrJ (ha.map f) (0 : S[X]) X
  · have h := congrArg (Polynomial.map f) (terminalInversePolynomial_equation W r I hI hrI ha)
    simp only [Polynomial.map_mul, Polynomial.map_add, Polynomial.map_C,
      Polynomial.map_comp, Polynomial.map_X] at h
    simpa only [algebraMap_eq, comp, map_zero, sub_zero, WeierstrassCurve.map_a₁] using h
  · simpa only [algebraMap_eq, comp, map_zero, sub_zero] using
      terminalInversePolynomial_equation (W.map f) (r.map f) J hJ hrJ (ha.map f)

variable (b3 b4 b6 : R)

/-- The complete residual product polynomial commutes with every coefficient homomorphism. -/
theorem terminalProductCorrection_map (F : R[X]) :
    (terminalProductCorrection b3 b4 b6 r F).map f =
      terminalProductCorrection (f b3) (f b4) (f b6) (r.map f) (F.map f) := by
  simp only [terminalProductCorrection, Polynomial.map_add, Polynomial.map_sub,
    Polynomial.map_mul, Polynomial.map_C, Polynomial.map_comp]

/-- The constructed inverse and the actual product correction restrict together. -/
theorem terminalConstructedCorrection_map :
    (terminalProductCorrection b3 b4 b6 r (terminalInversePolynomial W r I hI hrI ha)).map f =
      terminalProductCorrection (f b3) (f b4) (f b6) (r.map f)
        (terminalInversePolynomial (W.map f) (r.map f) J hJ hrJ (ha.map f)) := by
  rw [terminalProductCorrection_map, terminalInversePolynomial_map f W r I hI J hJ hf hrI ha]

end FLT.Mazur.WeierstrassDilatation
