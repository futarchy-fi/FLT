/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationPolynomialTangents
public import FLT.Mazur.NilpotentQuadraticRootNaturality

/-!
# The full terminal polynomial tangent root commutes with coefficient maps

Uniqueness compares the constructed roots even when the target nilpotent
ideal is larger than the image of the original ideal.
-/

@[expose] public noncomputable section
open Polynomial
namespace FLT.Mazur.WeierstrassDilatation
variable {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S)
  (I : Ideal R) (J : Ideal S) (hf : I ≤ J.comap f)

include hf in
/-- Coefficient restriction preserves the whole polynomial arithmetic ideal. -/
theorem terminalPolynomialIdeal_map :
    I.map C ≤ (J.map C).comap (Polynomial.mapRingHom f) := by
  intro p hp
  apply Ideal.mem_map_C_iff.mpr
  intro n
  change (p.map f).coeff n ∈ J
  rw [Polynomial.coeff_map]
  exact hf (Ideal.mem_map_C_iff.mp hp n)

variable (W : WeierstrassCurve R) (s : R) (hI : IsNilpotent I) (hJ : IsNilpotent J)
  (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)

/-- The complete polynomial tangent root is functorial in the original coefficients. -/
theorem terminalTangentRoot_map :
    (terminalTangentRoot W s I hI ha hs h2).map f =
      terminalTangentRoot (W.map f) (f s) J hJ (ha.map f) (hf hs) (hf h2) := by
  have h := NilpotentQuadraticRoot.root_map (I.map C)
    (NilpotentPolynomialInverse.mapIdeal_nilpotent I hI C) (J.map C)
    (NilpotentPolynomialInverse.mapIdeal_nilpotent J hJ C)
    (C W.a₁) (C W.a₂ + C s * X) (ha.map C) (terminalTangentConstant_mem W s I hs h2)
    (Polynomial.mapRingHom f) (terminalPolynomialIdeal_map f I J hf)
  simpa only [Polynomial.coe_mapRingHom, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_C, Polynomial.map_X, terminalTangentRoot, WeierstrassCurve.map_a₁,
    WeierstrassCurve.map_a₂] using h

end FLT.Mazur.WeierstrassDilatation
