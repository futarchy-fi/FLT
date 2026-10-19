/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelRationalCoordinates
public import FLT.Mazur.WeierstrassIntegralChart

/-!
# The rational affine chart of the source kernel

Quotienting by the infinity idempotent gives the actual affine part. Its
original coordinates satisfy the source cubic over the rational descended algebra.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace WeierstrassCurve.Velu

open FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The open and closed affine part removes exactly the identity idempotent. -/
abbrev PrimeKernelAffineAlgebra :=
  PrimeKernelDescentAlgebra E p q hq hfixed ⧸
    Ideal.span {primeKernelIdentity E p q hq hfixed}

/-- The original coordinate functions restricted to the affine part. -/
def primeKernelAffineQuotient : PrimeKernelDescentAlgebra E p q hq hfixed →ₐ[ℚ]
    PrimeKernelAffineAlgebra E p q hq hfixed := Ideal.Quotient.mkₐ ℚ _

@[simp] theorem primeKernelAffineQuotient_identity :
    primeKernelAffineQuotient E p q hq hfixed (primeKernelIdentity E p q hq hfixed) = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

/-- The rational affine coordinates satisfy the unmodified original source equation. -/
theorem primeKernelAffineQuotient_equation :
    (E.map (algebraMap ℚ (PrimeKernelAffineAlgebra E p q hq hfixed))).toAffine.Equation
      (primeKernelAffineQuotient E p q hq hfixed (primeKernelX E p q hq hfixed))
      (primeKernelAffineQuotient E p q hq hfixed (primeKernelY E p q hq hfixed)) := by
  apply (WeierstrassCurve.Affine.equation_iff _ _).mpr
  have h := congrArg (primeKernelAffineQuotient E p q hq hfixed)
    (primeKernel_affine_relation E p q hq hfixed)
  simpa only [map_add, map_mul, map_pow, AlgHom.commutes, map_sub, map_one,
    primeKernelAffineQuotient_identity, sub_zero, mul_one, WeierstrassCurve.toAffine,
    WeierstrassCurve.map] using h

/-- The actual map from the source cubic's affine chart algebra to its rational kernel algebra. -/
def primeKernelAffineChart : Coordinate E 2 →ₐ[ℚ] PrimeKernelAffineAlgebra E p q hq hfixed :=
  evaluation E 2
    ![primeKernelAffineQuotient E p q hq hfixed (primeKernelX E p q hq hfixed),
      primeKernelAffineQuotient E p q hq hfixed (primeKernelY E p q hq hfixed), 1]
    ((WeierstrassCurve.Projective.equation_some _ _).mpr
      (primeKernelAffineQuotient_equation E p q hq hfixed)) rfl

/-- The affine chart map uses the original abscissa function. -/
@[simp] theorem primeKernelAffineChart_x :
    primeKernelAffineChart E p q hq hfixed (coord E 2 0) =
      primeKernelAffineQuotient E p q hq hfixed (primeKernelX E p q hq hfixed) :=
  evaluation_coord _ _ _ _ _ _

/-- The affine chart map uses the original ordinate function. -/
@[simp] theorem primeKernelAffineChart_y :
    primeKernelAffineChart E p q hq hfixed (coord E 2 1) =
      primeKernelAffineQuotient E p q hq hfixed (primeKernelY E p q hq hfixed) :=
  evaluation_coord _ _ _ _ _ _

end WeierstrassCurve.Velu
