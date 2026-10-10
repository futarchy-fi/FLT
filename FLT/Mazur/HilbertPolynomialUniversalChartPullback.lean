/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPolynomialUniversalIdeal

/-!
# Recovering prescribed-basis families from the global universal ideal

Every chart parameter induces a map from its actual polynomial ambient
spectrum to the global ambient space. Pullback of the global universal ideal
along this map recovers its full polynomial quotient ideal.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w : Fin d → MvPolynomial I R)
variable {S : Type u} [CommRing S] [Algebra R S]

/-- Cache the coefficient ring for ambient parameter inference. -/
local instance parameterAmbientCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the parameter chart ring for polynomial ring inference. -/
local instance parameterAmbientChartRing : CommRing (ChartRing R I d w) := inferInstance

/-- A chart parameter induces an actual map of ambient polynomial spaces. -/
def polynomialParameterAmbientMap (a : ChartRing R I d w →ₐ[R] S) :
    Spec (.of (MvPolynomial I S)) ⟶ polynomialHilbertAmbient R I d :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map a.toRingHom)) ≫
    polynomialHilbertAmbientChart R I d w

/-- The induced ambient map lies over the corresponding glued chart parameter. -/
@[reassoc]
theorem polynomialParameterAmbientMap_fst (a : ChartRing R I d w →ₐ[R] S) :
    polynomialParameterAmbientMap R I d w a ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (MvPolynomial.C : S →+* MvPolynomial I S)) ≫
        Spec.map (CommRingCat.ofHom a.toRingHom) ≫ polynomialHilbertChartι R I d w := by
  rw [polynomialParameterAmbientMap, Category.assoc, polynomialHilbertAmbientChart_fst]
  simp only [← Category.assoc]
  congr 1
  rw [chartPolynomialProjection, ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro r
  exact MvPolynomial.map_C a.toRingHom r

/-- Pullback of the global universal ideal along any chart parameter recovers its ideal. -/
theorem polynomialUniversalIdeal_parameterPullback (a : ChartRing R I d w →ₐ[R] S) :
    (polynomialUniversalIdeal R I d).comap (polynomialParameterAmbientMap R I d w a) =
      baseIdeal (.of (MvPolynomial I S)) (pointIdeal R I d w a) := by
  rw [polynomialParameterAmbientMap, Scheme.IdealSheafData.comap_comp,
    polynomialUniversalIdeal_chart, chartPolynomialIdealSheaf, baseIdeal_comap_specMap]
  exact congrArg (baseIdeal (.of (MvPolynomial I S))) (chartIdentityIdeal_map R I d w a)

/-- Every prescribed-basis quotient is the actual pullback of the global universal ideal. -/
theorem polynomialUniversalIdeal_prescribedPullback (J : PrescribedBasisIdeals R I d w S) :
    (polynomialUniversalIdeal R I d).comap
        (polynomialParameterAmbientMap R I d w (idealClassifyingMap R I d w S J)) =
      baseIdeal (.of (MvPolynomial I S)) J.val := by
  rw [polynomialUniversalIdeal_parameterPullback]
  exact congrArg (baseIdeal (.of (MvPolynomial I S)))
    (congrArg Subtype.val (idealOfPoint_idealClassifyingMap R I d w S J))

end FLT.Mazur.HilbertChart
