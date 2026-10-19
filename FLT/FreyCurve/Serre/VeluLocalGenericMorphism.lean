/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluPrimeRationalGroup
public import FLT.FreyCurve.Serre.VeluPrimeRationalDegree
public import FLT.Mazur.WeierstrassGroupHomCoefficient
public import FLT.Mazur.WeierstrassGroupHomVariableChange

/-!
# The original prime quotient on specified local generic models

Extend the actual rational group homomorphism to the local field, then use the
specified source and target variable changes. The resulting map has degree p
and recovers the original rational map through the actual coefficient maps.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
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
local instance primeLocalGenericFintype :
    Fintype (show AddSubgroup (EQ).toAffine.Point from GQ) :=
  inferInstanceAs (Fintype (torsionKernel E p q))

variable (V : WeierstrassCurve ℚ)
  (hcurve : V.map (algebraMap ℚ (AlgebraicClosure ℚ)) =
    @curve (AlgebraicClosure ℚ) inferInstance inferInstance
      (E.map (algebraMap ℚ (AlgebraicClosure ℚ))) (torsionKernel E p q)
      (primeLocalGenericFintype E p q))
  (hfixed : ∀ g t, q (E.torsionGaloisRepresentation p g t) = q t)

variable {K R : Type} [Field K] [CommRing R] [Algebra ℚ K] [Algebra R K]
  (W U : WeierstrassCurve R) (C D : VariableChange K)
  (hC : C • E.map (algebraMap ℚ K) = W.map (algebraMap R K))
  (hD : D • V.map (algebraMap ℚ K) = U.map (algebraMap R K))

include hC in
omit [Fact p.Prime] in
/-- The prescribed source generic model is elliptic by its actual coordinate change. -/
theorem primeLocalSource_isElliptic : (W.map (algebraMap R K)).IsElliptic := by
  rw [← hC]
  infer_instance

/-- The rational prime quotient on the original coefficient-extended cubics. -/
def primeCoefficientGroupHom :
    integralCurveGroup (E.map (algebraMap ℚ K)) IsElliptic.isUnit ⟶
      integralCurveGroup (V.map (algebraMap ℚ K))
        (by let _ := torsionQuotient_isElliptic E p q hp V hcurve
            exact IsElliptic.isUnit) := by
  let _ := torsionQuotient_isElliptic E p q hp V hcurve
  exact integralGroupHomCoefficient E V IsElliptic.isUnit IsElliptic.isUnit
    IsElliptic.isUnit IsElliptic.isUnit (primeRationalGroupHom E p q hp V hcurve hfixed)

/-- Its coefficient square retains the original rational quotient. -/
@[reassoc] theorem primeCoefficientGroupHom_square :
    (primeCoefficientGroupHom (K := K) E p q hp V hcurve hfixed).hom.hom.hom.left ≫
        integralCoefficientMorphism V =
      integralCoefficientMorphism E ≫ primeRationalMorphism E p q hp V hcurve hfixed :=
  integralGroupHomCoefficient_square E V _ _ _ _ _

/-- The original rational map has this actual Cartesian local-field pullback. -/
theorem primeCoefficientGroupHom_isPullback :
    IsPullback (integralCoefficientMorphism E)
      (primeCoefficientGroupHom (K := K) E p q hp V hcurve hfixed).hom.hom.hom.left
      (primeRationalMorphism E p q hp V hcurve hfixed) (integralCoefficientMorphism V) :=
  integralGroupHomCoefficient_isPullback E V _ _ _ _ _

/-- The coefficient-extended quotient still has exactly prime degree. -/
theorem primeCoefficientGroupHom_degree (hq : Function.Surjective q) :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree
      (primeCoefficientGroupHom (K := K) E p q hp V hcurve hfixed).hom.hom.hom.left p :=
  integralGroupHomCoefficient_degree E V _ _ _ _ _ p
    (primeRationalMorphism_degree E p q hp V hcurve hfixed hq)

/-- The original prime morphism on the specified integral models' generic fibers. -/
def primeLocalGenericGroupHom :
    integralCurveGroup (W.map (algebraMap R K)) (primeLocalSource_isElliptic E W C hC).isUnit ⟶
      integralCurveGroup (U.map (algebraMap R K))
        (by
      let _ := torsionQuotient_isElliptic E p q hp V hcurve
      exact (primeLocalSource_isElliptic V U D hD).isUnit) :=
  integralGroupHomVariableChange _ _ _ _ C D hC hD _ _
    (primeLocalSource_isElliptic E W C hC).isUnit
    (by
      let _ := torsionQuotient_isElliptic E p q hp V hcurve
      exact (primeLocalSource_isElliptic V U D hD).isUnit)
    (primeCoefficientGroupHom E p q hp V hcurve hfixed)

/-- The actual local coordinate changes recover the original coefficient-extended map. -/
@[reassoc] theorem primeLocalGenericGroupHom_square :
    (primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD).hom.hom.hom.left ≫
        (integralVariableChangeIso _ _ D hD).hom =
      (integralVariableChangeIso _ _ C hC).hom ≫
        (primeCoefficientGroupHom (K := K) E p q hp V hcurve hfixed).hom.hom.hom.left :=
  integralGroupHomVariableChange_square _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The exact generic coordinate changes form the actual Cartesian quotient square. -/
theorem primeLocalGenericGroupHom_isPullback :
    IsPullback (integralVariableChangeIso _ _ C hC).hom
      (primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD).hom.hom.hom.left
      (primeCoefficientGroupHom (K := K) E p q hp V hcurve hfixed).hom.hom.hom.left
      (integralVariableChangeIso _ _ D hD).hom :=
  integralGroupHomVariableChange_isPullback _ _ _ _ _ _ _ _ _ _ _ _ _

/-- The composite square recovers the actual rational quotient from the specified local models. -/
@[reassoc] theorem primeLocalGenericGroupHom_rational_square :
    (primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD).hom.hom.hom.left ≫
        (integralVariableChangeIso _ _ D hD).hom ≫ integralCoefficientMorphism V =
      (integralVariableChangeIso _ _ C hC).hom ≫ integralCoefficientMorphism E ≫
        primeRationalMorphism E p q hp V hcurve hfixed := by
  rw [primeLocalGenericGroupHom_square_assoc, primeCoefficientGroupHom_square]

/-- Both prescribed local minimalizations preserve the actual degree p. -/
theorem primeLocalGenericGroupHom_degree (hq : Function.Surjective q) :
    FLT.Mazur.FCurve.FiniteLocallyFreeDegree
      (primeLocalGenericGroupHom E p q hp V hcurve hfixed W U C D hC hD).hom.hom.hom.left p :=
  integralGroupHomVariableChange_degree _ _ _ _ _ _ _ _ _ _ _ _ _ p
    (primeCoefficientGroupHom_degree E p q hp V hcurve hfixed hq)

end WeierstrassCurve.Velu
