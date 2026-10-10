/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteLocallyFreeDegreeCover
public import FLT.Mazur.HilbertAmbientQuotientEvaluation
public import FLT.Mazur.HilbertPolynomialQuotientBaseChange
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Actual closed finite families in an arbitrary affine ambient scheme

Every point of the closed relation chart gives a closed immersion into the
actual tensor base change of the original affine quotient scheme. The
projection has finite locally free degree from its constructed free basis.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped TensorProduct

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R I : Type u) [CommRing R] (d : ℕ)
variable (w : Fin d → MvPolynomial I R) (K : Ideal (MvPolynomial I R))

/-- Cache the coefficient ring for the actual closed ambient family. -/
local instance ambientClosedCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the chart ring for the actual closed ambient family. -/
local instance ambientClosedChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- Cache the original affine quotient ring for tensor spectrum maps. -/
local instance ambientClosedQuotientRing : CommRing (MvPolynomial I R ⧸ K) := inferInstance

variable (S : Type u) [CommRing S] [Algebra R S]
variable (g : AmbientChartRing R I d w K →ₐ[R] S)

/-- The evaluation from the actual base-changed affine ambient algebra. -/
def ambientTensorPointEvaluation : S ⊗[R] (MvPolynomial I R ⧸ K) →ₐ[S]
    PointFiber R I d w (ambientChartForget R I d w K S g) :=
  (ambientPointEvaluation R I d w K S g).comp
    (polynomialQuotientBaseChangeEquiv I R S K).toAlgHom

/-- The actual tensor-ambient evaluation is surjective. -/
theorem ambientTensorPointEvaluation_surjective :
    Function.Surjective (ambientTensorPointEvaluation R I d w K S g) :=
  (ambientPointEvaluation_surjective R I d w K S g).comp
    (polynomialQuotientBaseChangeEquiv I R S K).surjective

/-- The actual closed family lies inside the base change of the original affine quotient scheme. -/
def ambientPointClosedImmersion :
    Spec (.of (PointFiber R I d w (ambientChartForget R I d w K S g))) ⟶
      Spec (.of (S ⊗[R] (MvPolynomial I R ⧸ K))) :=
  Spec.map (CommRingCat.ofHom (ambientTensorPointEvaluation R I d w K S g).toRingHom)

/-- Surjective ambient evaluation gives a scheme-theoretic closed immersion. -/
instance ambientPointClosedImmersion_isClosedImmersion :
    IsClosedImmersion (ambientPointClosedImmersion R I d w K S g) :=
  IsClosedImmersion.spec_of_surjective _ (ambientTensorPointEvaluation_surjective R I d w K S g)

/-- The tensor ambient space is the actual base change of the original quotient scheme. -/
theorem ambientPointSpace_isPullback :
    IsPullback
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] (MvPolynomial I R ⧸ K))))
      (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : (MvPolynomial I R ⧸ K) →ₐ[R]
          S ⊗[R] (MvPolynomial I R ⧸ K)).toRingHom))
      (Spec.map (CommRingCat.ofHom (algebraMap R S)))
      (Spec.map (CommRingCat.ofHom (algebraMap R (MvPolynomial I R ⧸ K)))) :=
  isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct R S (MvPolynomial I R ⧸ K))

/-- The actual closed immersion respects the projection to the test base. -/
theorem ambientPointClosedImmersion_over :
    ambientPointClosedImmersion R I d w K S g ≫
        Spec.map (CommRingCat.ofHom
          (Algebra.TensorProduct.includeLeftRingHom : S →+* S ⊗[R] (MvPolynomial I R ⧸ K))) =
      Spec.map (CommRingCat.ofHom
        (algebraMap S (PointFiber R I d w (ambientChartForget R I d w K S g)))) := by
  rw [ambientPointClosedImmersion, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact (ambientTensorPointEvaluation R I d w K S g).commutes r

/-- The actual closed family has finite locally free degree `d` over the test base. -/
theorem ambientPointClosedFamily_degree :
    FCurve.FiniteLocallyFreeDegree
      (Spec.map (CommRingCat.ofHom
        (algebraMap S (PointFiber R I d w (ambientChartForget R I d w K S g))))) d :=
  FCurve.finiteLocallyFreeDegree_spec_of_basis S _ d
    (pointBasis R I d w (ambientChartForget R I d w K S g))

end FLT.Mazur.HilbertChart
