/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluGlobalGaloisInvariant
public import FLT.FreyCurve.Serre.VeluPrimeGlobalKernelRank
public import FLT.FreyCurve.Serre.VeluPrimeKernelFiberComparison

/-!
# The original prime Vélu morphism on the exact rational target

The equality hcurve identifies the actual geometric target, with its degree
and original Cartesian kernel intact. Projection to the rational target is
invariant as a whole scheme morphism under the original Galois action.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Limits
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q) [Fintype (torsionKernel E p q)] (hp : Odd p)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Cache the original finite subgroup on the mapped cubic. -/
local instance primeExactTargetFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (primeExactTargetFintype E p q))

local notation "VQ" => V.map (algebraMap ℚ (AlgebraicClosure ℚ))

/-- The actual degree-p morphism with the exact rational equation as geometric target. -/
def primeGlobalToExactTarget : integralCurve EQ ⟶ integralCurve VQ :=
  veluGlobalToEquation EQ GQ (torsionKernel_ne_neg E p q hp) VQ hcurve

include hq in
/-- The exact target transport retains the actual finite locally free degree p. -/
theorem primeGlobalToExactTarget_degree :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree (primeGlobalToExactTarget E p q hp V hcurve) p := by
  have h := veluGlobalToEquation_degree EQ GQ (torsionKernel_ne_neg E p q hp) VQ hcurve
  have hc : Nat.card (show AddSubgroup (EQ).toAffine.Point from GQ) = p :=
    torsionKernel_card_prime E p q hq
  rw [hc] at h
  exact h

/-- The original geometric closed subgroup is still the actual Cartesian identity fiber. -/
theorem primeGlobalToExactTarget_kernel :
    IsPullback (primeKernelClosedSubgroup E p q hq).inclusion.left
      (primeKernelClosedSubgroup E p q hq).carrier.hom
      (primeGlobalToExactTarget E p q hp V hcurve) (integralCurveZero VQ) := by
  have h (W : WeierstrassCurve (AlgebraicClosure ℚ)) (hW : W = curve EQ GQ) :
      IsPullback (primeKernelClosedSubgroup E p q hq).inclusion.left
        (primeKernelClosedSubgroup E p q hq).carrier.hom
        (veluGlobalToEquation EQ GQ (torsionKernel_ne_neg E p q hp) W hW)
        (integralCurveZero W) := by
    subst W
    simpa only [veluGlobalToEquation, eqToHom_refl, Category.comp_id] using
      primeKernelClosedSubgroup_global_isPullback E p q hq hp
  exact h VQ hcurve

/-- Project the actual geometric quotient to the original rational target. -/
def primeGlobalToRationalTarget : integralCurve EQ ⟶ integralCurve V :=
  veluGlobalToBaseTarget E GQ (torsionKernel_ne_neg E p q hp) V hcurve

/-- The rational target projection retains the actual finite geometric map. -/
theorem primeGlobalToRationalTarget_factor :
    primeGlobalToRationalTarget E p q hp V hcurve =
      primeGlobalToExactTarget E p q hp V hcurve ≫ integralCoefficientMorphism V := rfl

/-- The original whole geometric morphism to the rational target is Galois invariant. -/
theorem primeGlobalToRationalTarget_galois
    (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)
    (g : Field.absoluteGaloisGroup ℚ) :
    integralGaloisMap E g ≫ primeGlobalToRationalTarget E p q hp V hcurve =
      primeGlobalToRationalTarget E p q hp V hcurve :=
  veluGlobalToBaseTarget_galois E GQ (torsionKernel_ne_neg E p q hp) V hcurve
    (torsionKernel_stable E p q hfixed) g

end WeierstrassCurve.Velu
