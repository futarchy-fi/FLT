/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluDescendedMorphism
public import FLT.FreyCurve.Serre.VeluPrimeExactTarget

/-!
# The actual rational prime Vélu morphism

The original Galois-fixed torsion quotient now gives a morphism between the
original rational cubics. Its coefficient square retains the exact hcurve
target and the original degree-p geometric Vélu map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  [Fintype (torsionKernel E p q)] (hp : Odd p)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Cache the same original finite subgroup on the mapped source cubic. -/
local instance primeDescendedFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (primeDescendedFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The original prime map descended to the exact original rational source and target. -/
def primeRationalMorphism : integralCurve E ⟶ integralCurve V :=
  veluDescendedMorphism E GQ (torsionKernel_ne_neg E p q hp) V hcurve
    (torsionKernel_stable E p q hfixed)

/-- Coefficient projection recovers the original whole geometric morphism to the target. -/
@[reassoc] theorem primeRationalMorphism_fac :
    integralCoefficientMorphism E ≫ primeRationalMorphism E p q hp V hcurve hfixed =
      primeGlobalToRationalTarget E p q hp V hcurve := veluDescendedMorphism_fac ..

/-- The rational morphism lies over the original rational field. -/
@[reassoc] theorem primeRationalMorphism_base :
    primeRationalMorphism E p q hp V hcurve hfixed ≫ integralCurveStructure V =
      integralCurveStructure E := veluDescendedMorphism_base ..

/-- The exact hcurve geometric map is the actual Cartesian coefficient pullback. -/
theorem primeRationalMorphism_isPullback :
    IsPullback (integralCoefficientMorphism E) (primeGlobalToExactTarget E p q hp V hcurve)
      (primeRationalMorphism E p q hp V hcurve hfixed) (integralCoefficientMorphism V) :=
  veluDescendedMorphism_isPullback ..

/-- The rational identity is carried to the exact rational target identity. -/
@[reassoc] theorem primeRationalMorphism_zero :
    integralCurveZero E ≫ primeRationalMorphism E p q hp V hcurve hfixed =
      integralCurveZero V := veluDescendedMorphism_zero ..

/-- The rational morphism is uniquely specified by its original geometric map. -/
theorem primeRationalMorphism_unique (f : integralCurve E ⟶ integralCurve V)
    (hf : integralCoefficientMorphism E ≫ f = primeGlobalToRationalTarget E p q hp V hcurve) :
    f = primeRationalMorphism E p q hp V hcurve hfixed :=
  veluDescendedMorphism_unique E GQ (torsionKernel_ne_neg E p q hp) V hcurve
    (torsionKernel_stable E p q hfixed) f hf

end WeierstrassCurve.Velu
