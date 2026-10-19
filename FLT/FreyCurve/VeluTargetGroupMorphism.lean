/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluPrimeRationalGroup
public import FLT.FreyCurve.Serre.VeluPrimeRationalPointComparison
public import FLT.FreyCurve.VeluTargetSchemeMorphism

/-!
# The retained Frey target receives the actual rational group quotient

The same map has prime degree, the original closed kernel, and the original
rational point quotient. Both point-level descent squares are retained, so
the target torsion embedding remains tied to the original geometric quotient.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry WeierstrassCurve WeierstrassCurve.Velu
open FLT.Mazur.WeierstrassIntegralChart

namespace FreyPackage

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {P : FreyPackage} {E : WeierstrassCurve ℚ}

/-- The original nonidentity target has a compatible scheme and point quotient. -/
theorem IsVeluTarget.exists_prime_group_morphism (h : P.IsVeluTarget E)
    (hne : E ≠ P.freyCurve) :
    have _ : Fact P.p.Prime := ⟨P.pp⟩
    ∃ (q : (P.freyCurve.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion P.p →ₗ[ZMod P.p]
        ZMod P.p) (hq : Function.Surjective q)
      (hfixed : ∀ g t, q (P.freyCurve.torsionGaloisRepresentation P.p g t) = q t)
      (heq : Velu.TorsionQuotientEquation P.freyCurve P.p P.hppos q E)
      (hE : E.IsElliptic)
      (F : integralCurveGroup P.freyCurve IsElliptic.isUnit ⟶ integralCurveGroup E hE.isUnit)
      (φ : (P.freyCurve.toAffine.baseChange ℚ).Point →+ (E.toAffine.baseChange ℚ).Point)
      (f : ZMod P.p →+ (E.toAffine.baseChange ℚ).Point),
      FLT.Mazur.FCurve.FiniteLocallyFreeDegree F.hom.hom.hom.left P.p ∧
      IsPullback (Velu.primeKernelRationalMap P.freyCurve P.p q hq hfixed)
        (Velu.primeKernelRationalScheme P.freyCurve P.p q hq hfixed).hom
        F.hom.hom.hom.left (integralCurveZero E) ∧
      (∀ a, φ a = 0 → P.p • a = 0) ∧ Function.Injective f ∧
      (∀ a, (affineSmoothPoint P.freyCurve a ≫ (integralSmoothOpen P.freyCurve).ι) ≫
        F.hom.hom.hom.left = affineSmoothPoint E (φ a) ≫ (integralSmoothOpen E).ι) ∧
      (∀ a, Affine.Point.baseChange (W' := E.toAffine) ℚ (AlgebraicClosure ℚ) (φ a) =
        Velu.torsionQuotientPointHom P.freyCurve P.p P.hppos q P.hp_odd E heq
          (Affine.Point.baseChange (W' := P.freyCurve.toAffine) ℚ (AlgebraicClosure ℚ) a)) ∧
      (∀ t, Affine.Point.baseChange (W' := E.toAffine) ℚ (AlgebraicClosure ℚ) (f (q t)) =
        Velu.torsionQuotientPointHom P.freyCurve P.p P.hppos q P.hp_odd E heq t.val) := by
  classical
  dsimp only
  let _ : Fact P.p.Prime := ⟨P.pp⟩
  rcases h with heq | ⟨q, hq, hfixed, heq⟩
  · exact (hne heq).elim
  · let _ : Fintype (Velu.torsionKernel P.freyCurve P.p q) :=
      @Fintype.ofFinite _ (Velu.torsionKernel_finite P.freyCurve P.p q P.hppos)
    obtain ⟨φ, f, hφ, hf, hφgeom, hfgeom⟩ :=
      Velu.rational_maps_of_torsionQuotientEquation P.freyCurve P.p P.hppos q
        P.hp_odd E heq hq hfixed
    refine ⟨q, hq, hfixed, heq, Velu.torsionQuotient_isElliptic P.freyCurve P.p q P.hp_odd E heq,
      Velu.primeRationalGroupHom P.freyCurve P.p q P.hp_odd E heq hfixed,
      φ, f, Velu.primeRationalMorphism_degree P.freyCurve P.p q P.hp_odd E heq hfixed hq,
      Velu.primeRationalMorphism_kernel P.freyCurve P.p q P.hp_odd E heq hfixed hq,
      hφ, hf, ?_, hφgeom, hfgeom⟩
    exact Velu.primeRationalMorphism_rationalPoint P.freyCurve P.p q P.hp_odd E heq hfixed
      φ hφgeom

end FreyPackage
