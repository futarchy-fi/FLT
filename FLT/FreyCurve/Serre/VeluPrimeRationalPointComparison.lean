/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluDescendedPointValues
public import FLT.FreyCurve.Serre.VeluPrimeRationalMorphism
public import FLT.FreyCurve.Serre.QuotientCoordinateHom
public import FLT.FreyCurve.Serre.VeluPrimeExactTarget

/-!
# The rational scheme map agrees with the original quotient on points

The actual prime morphism induces the retained geometric coordinate homomorphism.
Every rational point quotient with its original base-change square therefore
agrees with this scheme map, including the descended quotient-line embedding.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (E : WeierstrassCurve ℚ) [E.IsElliptic] (p : ℕ) [Fact p.Prime]
  (q : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p →ₗ[ZMod p] ZMod p)
  (hp : Odd p) (V : WeierstrassCurve ℚ)
  (hcurve : TorsionQuotientEquation E p (Nat.Prime.pos Fact.out) q V)
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

local notation "EQ" => E.map (algebraMap ℚ (AlgebraicClosure ℚ))
local notation "GQ" => torsionKernel E p q

/-- Use the same canonical finite enumeration as the original point quotient. -/
local instance primeRationalPointFintype : Fintype (torsionKernel E p q) :=
  @Fintype.ofFinite _ (torsionKernel_finite E p q (Nat.Prime.pos Fact.out))

/-- Cache the original enumeration on the actual mapped cubic. -/
local instance primeRationalPointMappedFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  primeRationalPointFintype E p q

/-- The scheme map induces the original geometric torsion quotient homomorphism. -/
@[reassoc] theorem primeRationalMorphism_pointHom
    (P : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).toAffine.Point) :
    (affineSmoothPoint E P ≫ (integralSmoothOpen E).ι) ≫
        primeRationalMorphism E p q hp V hcurve hfixed =
      affineSmoothPoint V
        (torsionQuotientPointHom E p (Nat.Prime.pos Fact.out) q hp V hcurve P) ≫
          (integralSmoothOpen V).ι :=
  veluDescendedMorphism_pointMap E GQ (torsionKernel_ne_neg E p q hp) V hcurve
    (torsionKernel_stable E p q hfixed) (torsionKernel_landing E p q hp V hcurve) P

/-- Any retained rational quotient map agrees with the actual rational scheme morphism. -/
@[reassoc] theorem primeRationalMorphism_rationalPoint
    (φ : (E.toAffine.baseChange ℚ).Point →+ (V.toAffine.baseChange ℚ).Point)
    (hφ : ∀ a, Affine.Point.baseChange (W' := V.toAffine) ℚ (AlgebraicClosure ℚ) (φ a) =
      torsionQuotientPointHom E p (Nat.Prime.pos Fact.out) q hp V hcurve
        (Affine.Point.baseChange (W' := E.toAffine) ℚ (AlgebraicClosure ℚ) a))
    (a : (E.toAffine.baseChange ℚ).Point) :
    (affineSmoothPoint E a ≫ (integralSmoothOpen E).ι) ≫
        primeRationalMorphism E p q hp V hcurve hfixed =
      affineSmoothPoint V (φ a) ≫ (integralSmoothOpen V).ι :=
  veluDescendedMorphism_basePoint E GQ (torsionKernel_ne_neg E p q hp) V hcurve
    (torsionKernel_stable E p q hfixed) (torsionKernel_landing E p q hp V hcurve)
    a (φ a) (hφ a)

/-- The original quotient-line embedding is the image of the original geometric torsion. -/
@[reassoc] theorem primeRationalMorphism_quotientTorsion
    (f : ZMod p →+ (V.toAffine.baseChange ℚ).Point)
    (hf : ∀ t, Affine.Point.baseChange (W' := V.toAffine) ℚ (AlgebraicClosure ℚ) (f (q t)) =
      torsionQuotientPointHom E p (Nat.Prime.pos Fact.out) q hp V hcurve t.val)
    (t : (E.map (algebraMap ℚ (AlgebraicClosure ℚ))).nTorsion p) :
    (affineSmoothPoint E t.val ≫ (integralSmoothOpen E).ι) ≫
        primeRationalMorphism E p q hp V hcurve hfixed =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ (AlgebraicClosure ℚ))) ≫
        (affineSmoothPoint V (f (q t)) ≫ (integralSmoothOpen V).ι) := by
  rw [primeRationalMorphism_pointHom]
  change _ = Spec.map (CommRingCat.ofHom (Algebra.ofId ℚ (AlgebraicClosure ℚ)).toRingHom) ≫ _
  rw [affineSmoothPoint_natural V (Algebra.ofId ℚ (AlgebraicClosure ℚ))]
  exact congrArg (fun P ↦ affineSmoothPoint V P ≫ (integralSmoothOpen V).ι) (hf t).symm

end WeierstrassCurve.Velu
