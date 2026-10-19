/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluPrimeRationalKernel
public import FLT.FreyCurve.VeluTargetWitness

/-!
# Actual degree-p scheme morphisms for the retained Frey target equations

A nonidentity target from the existing Frey witness receives the constructed
rational Vélu morphism. Its degree and original rational closed kernel are
proved, with no replacement of the target equation or torsion quotient.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry WeierstrassCurve
open FLT.Mazur.WeierstrassIntegralChart

namespace FreyPackage

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- Every original nonidentity Frey target receives a degree-p map with its original kernel. -/
theorem IsVeluTarget.exists_prime_scheme_morphism (h : P.IsVeluTarget E)
    (hne : E ≠ P.freyCurve) :
    have _ : Fact P.p.Prime := ⟨P.pp⟩
    ∃ (q : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p →ₗ[ZMod P.p]
        ZMod P.p) (hq : Function.Surjective q)
      (hfixed : ∀ g t, q (P.freyCurve.torsionGaloisRepresentation P.p g t) = q t)
      (f : integralCurve P.freyCurve ⟶ integralCurve E),
      f ≫ integralCurveStructure E = integralCurveStructure P.freyCurve ∧
      integralCurveZero P.freyCurve ≫ f = integralCurveZero E ∧
      FLT.Mazur.FCurve.FiniteLocallyFreeDegree f P.p ∧
      IsPullback (Velu.primeKernelRationalMap P.freyCurve P.p q hq hfixed)
        (Velu.primeKernelRationalScheme P.freyCurve P.p q hq hfixed).hom
        f (integralCurveZero E) := by
  classical
  dsimp only
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  rcases h with heq | ⟨q, hq, hfixed, heq⟩
  · exact (hne heq).elim
  · let _ : Fintype (Velu.torsionKernel P.freyCurve P.p q) :=
      @Fintype.ofFinite _ (Velu.torsionKernel_finite P.freyCurve P.p q P.hppos)
    refine ⟨q, hq, hfixed,
      Velu.primeRationalMorphism P.freyCurve P.p q P.hp_odd E heq hfixed,
      Velu.primeRationalMorphism_base P.freyCurve P.p q P.hp_odd E heq hfixed,
      Velu.primeRationalMorphism_zero P.freyCurve P.p q P.hp_odd E heq hfixed,
      Velu.primeRationalMorphism_degree P.freyCurve P.p q P.hp_odd E heq hfixed hq,
      Velu.primeRationalMorphism_kernel P.freyCurve P.p q P.hp_odd E heq hfixed hq⟩

end FreyPackage
