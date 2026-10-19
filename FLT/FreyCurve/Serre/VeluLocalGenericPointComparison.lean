/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluLocalPointMorphism
public import FLT.FreyCurve.Serre.VeluLocalGenericMorphism
public import FLT.FreyCurve.Serre.VeluPrimeRationalPointComparison
public import FLT.Mazur.WeierstrassLocalGenericProjection

/-!
# The local generic quotient agrees with the retained rational point quotient

The original rational point square and the actual local coefficient square
identify the local scheme map on the specified transported points.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur FLT.Mazur.WeierstrassIntegralChart

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
local instance localPointComparisonFintype : Fintype (torsionKernel E p q) :=
  @Fintype.ofFinite _ (torsionKernel_finite E p q (Nat.Prime.pos Fact.out))

/-- Cache the original enumeration on the actual mapped cubic. -/
local instance localPointComparisonMappedFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  localPointComparisonFintype E p q


variable {L R : Type} [Field L] [CommRing R] [Algebra ℚ L] [Algebra R L]
  [DecidableEq L] (W U : WeierstrassCurve R) (C D : VariableChange L)
  (hC : C • E.map (algebraMap ℚ L) = W.map (algebraMap R L))
  (hD : D • V.map (algebraMap ℚ L) = U.map (algebraMap R L))

/-- Every specified transported rational point follows the actual local generic morphism. -/
@[reassoc] theorem primeLocalGenericGroupHom_rationalPoint
    (φ : (E.toAffine.baseChange ℚ).Point →+ (V.toAffine.baseChange ℚ).Point)
    (hφ : ∀ a, Affine.Point.baseChange (W' := V.toAffine) ℚ (AlgebraicClosure ℚ) (φ a) =
      torsionQuotientPointHom E p (Nat.Prime.pos Fact.out) q hp V hcurve
        (Affine.Point.baseChange (W' := E.toAffine) ℚ (AlgebraicClosure ℚ) a))
    (a : (E.toAffine.baseChange ℚ).Point) :
    let _ := torsionQuotient_isElliptic E p q hp V hcurve
    (affineSmoothPoint (W.map (algebraMap R L))
        (ellipticExtensionPointHom (K := ℚ) E W C hC a) ≫
          (integralSmoothOpen (W.map (algebraMap R L))).ι) ≫
            (primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD).hom.hom.hom.left =
      affineSmoothPoint (U.map (algebraMap R L))
        (ellipticExtensionPointHom (K := ℚ) V U D hD (φ a)) ≫
          (integralSmoothOpen (U.map (algebraMap R L))).ι := by
  let _ := torsionQuotient_isElliptic E p q hp V hcurve
  exact ellipticExtensionPointHom_morphism E V W U C D hC hD
    (primeRationalMorphism E p q hp V hcurve hfixed)
    (primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD).hom.hom.hom.left
    (primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD).hom.hom.hom.w
    (by
      simpa only [localGenericProjection, Category.assoc] using
        primeLocalGenericGroupHom_rational_square E p q hp V hcurve hfixed W U C D hC hD)
    a (φ a) (primeRationalMorphism_rationalPoint E p q hp V hcurve hfixed φ hφ a)

end WeierstrassCurve.Velu
