/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluKernelInclusionMultiplication

/-!
# The original rational source kernel as a finite subgroup

The actual inclusion, its proved multiplication compatibility and closedness,
and its computed degree supply a finite locally free subgroup of the original
rational cubic. The geometric inclusion is its Cartesian coefficient extension.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace WeierstrassCurve.Velu

open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hq : Function.Surjective q)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

/-- The original descended kernel is a closed finite locally free subgroup of rank p. -/
def primeKernelRationalSubgroup :
    (integralGeneralizedEllipticCurve E E.isUnit_Δ).FiniteSubgroup p where
  carrier := primeKernelRationalScheme E p q hq hfixed
  inclusion := primeKernelRationalInclusion E p q hq hfixed
  closed := primeKernelRationalMap_closed E p q hq hfixed
  degree := primeKernelRationalScheme_degree E p q hq hfixed

/-- The constructed rational finite subgroup is etale. -/
instance primeKernelRationalSubgroup_etale :
    Etale (primeKernelRationalSubgroup E p q hq hfixed).carrier.hom :=
  primeKernelRationalScheme_etale E p q hq hfixed

/-- Its inclusion is the original rational kernel map, with no replacement of the carrier. -/
theorem primeKernelRationalSubgroup_inclusion :
    (primeKernelRationalSubgroup E p q hq hfixed).inclusion.left =
      primeKernelRationalMap E p q hq hfixed := rfl

/-- The original geometric subgroup is the actual Cartesian base change of this inclusion. -/
theorem primeKernelRationalSubgroup_isPullback :
    IsPullback (primeKernelClosedSubgroup E p q hq).inclusion.left
      ((primeKernelPullbackIso E p q hq hfixed).hom ≫ Limits.pullback.snd _ _)
      (integralCoefficientMorphism E)
      (primeKernelRationalSubgroup E p q hq hfixed).inclusion.left :=
  primeKernelRationalMap_isPullback E p q hq hfixed

end WeierstrassCurve.Velu
