/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.VeluTargetWitness
public import FLT.FreyCurve.Serre.VeluGeometricKernelScheme
public import FLT.FreyCurve.Serre.VeluKernelDescentAlgebra

/-!
# Actual Frey targets retain the constructed source kernel models

The same quotient that defines the target equation supplies the geometric
closed subgroup and the rational finite etale coordinate algebra. The source
curve and kernel remain fixed throughout these constructions.
-/

@[expose] public noncomputable section

open AlgebraicGeometry WeierstrassCurve
open scoped WeierstrassCurve.Affine

namespace FreyPackage

open FLT.Mazur.WeierstrassIntegralChart

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- Every nonidentity actual target retains both models of its original source kernel. -/
theorem IsVeluTarget.exists_source_kernel_models (h : P.IsVeluTarget E)
    (hne : E ≠ P.freyCurve) :
    letI : Fact P.p.Prime := ⟨P.pp⟩
    ∃ (q : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p →ₗ[ZMod P.p]
        ZMod P.p) (hq : Function.Surjective q)
      (hfixed : ∀ g t, q (P.freyCurve.torsionGaloisRepresentation P.p g t) = q t),
      Velu.TorsionQuotientEquation P.freyCurve P.p P.hppos q E ∧
      Etale (Velu.primeKernelClosedSubgroup P.freyCurve P.p q hq).carrier.hom ∧
      (∀ s, (Velu.primeKernelClosedSubgroup P.freyCurve P.p q hq).carrier.hom.finrank s =
        P.p) ∧
      Module.finrank ℚ (Velu.PrimeKernelDescentAlgebra P.freyCurve P.p q hq hfixed) = P.p := by
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  rcases h with heq | ⟨q, hq, hfixed, heq⟩
  · exact (hne heq).elim
  · exact ⟨q, hq, hfixed, heq,
      Velu.primeKernelClosedSubgroup_etale P.freyCurve P.p q hq,
      Velu.primeKernelClosedSubgroup_rank P.freyCurve P.p q hq,
      Velu.primeKernelDescentAlgebra_finrank P.freyCurve P.p q hq hfixed⟩

end FreyPackage
