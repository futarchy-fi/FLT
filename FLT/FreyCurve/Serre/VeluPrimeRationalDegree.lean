/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluDescendedDegree
public import FLT.FreyCurve.Serre.VeluPrimeRationalMorphism

/-!
# Degree p of the actual rational prime Vélu morphism

Surjectivity of the original torsion quotient computes the degree of the
constructed rational morphism, retaining the exact original target equation.
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
local instance primeRationalDegreeFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (primeRationalDegreeFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

variable (hq : Function.Surjective q)

include hq in
/-- The constructed rational morphism is finite locally free of the original prime degree. -/
theorem primeRationalMorphism_degree :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree
      (primeRationalMorphism E p q hp V hcurve hfixed) p := by
  have H := veluDescendedMorphism_degree E GQ (torsionKernel_ne_neg E p q hp) V hcurve
    (torsionKernel_stable E p q hfixed)
  have hc : Nat.card (show AddSubgroup (EQ).toAffine.Point from GQ) = p :=
    torsionKernel_card_prime E p q hq
  rw [hc] at H
  exact H

include hq in
/-- Every fiber over the exact rational target has rank p. -/
theorem primeRationalMorphism_rank (y : integralCurve V) :
    (primeRationalMorphism E p q hp V hcurve hfixed).finrank y = p :=
  (primeRationalMorphism_degree E p q hp V hcurve hfixed hq).2.2.2 y

end WeierstrassCurve.Velu
