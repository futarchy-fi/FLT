/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicLegendreBraidIntegral
public import FLT.EllipticCurve.CubicCoefficientNaturality

/-! # Comparing cyclic maps on the common Legendre cover

The common cyclic coefficient cover is an effective epimorphism.
It refines all three quadratic coefficient covers, including the
complementary-root cover, whose domain property follows from its
injective inclusion in the common domain.

A quadratic descended coordinate map pulls back to its actual coordinate
transport along any coefficient map into the common cover. Together with
the equality criterion, this supplies the comparison tools for global
relations; the mixed global relation itself is not asserted here.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace WeierstrassCurve.CubicCharts

instance legendreBraidCoverEffectiveEpi (p : ℕ) [NeZero p] :
    EffectiveEpi (legendreBraidCover p) := by infer_instance


open scoped TensorProduct
theorem braidThirdMap_injective (p : ℕ) [NeZero p] :
    Function.Injective
      (quadraticTripleThirdMap (-1 : (LegendreBase p)ˣ)
        (legendreParameterUnit p) (legendreComplementUnit p)) := by
  apply Algebra.TensorProduct.includeRight_injective
  exact FaithfulSMul.algebraMap_injective (LegendreBase p)
    (QuadraticEtaleRing (-1 : (LegendreBase p)ˣ) ⊗[LegendreBase p]
      QuadraticEtaleRing (legendreParameterUnit p))

instance legendreComplementDomain (p : ℕ) [NeZero p] :
    IsDomain (QuadraticEtaleRing (legendreComplementUnit p)) :=
  Function.Injective.isDomain
    (quadraticTripleThirdMap (-1 : (LegendreBase p)ˣ)
      (legendreParameterUnit p) (legendreComplementUnit p)) (braidThirdMap_injective p)

instance legendreComplementNoetherian (p : ℕ) :
    IsNoetherianRing (QuadraticEtaleRing (legendreComplementUnit p)) :=
  IsNoetherianRing.of_finite (LegendreBase p) _

instance legendreComplementLevelUnit (p : ℕ) :
    Fact (IsUnit (p : QuadraticEtaleRing (legendreComplementUnit p))) :=
  ⟨by
    simpa only [map_natCast] using
      (legendreBase_units p).2.1.map
        (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreComplementUnit p)))⟩

variable (p : ℕ) [Fact p.Prime]
variable (W : WeierstrassCurve (LegendreBase p)) [W.IsElliptic]

/-- The common cyclic coefficient scheme identified with the scheme pullback. -/
def braidCyclicPullbackIso :
    (scalarQuotientModel (W.map (algebraMap (LegendreBase p) (LegendreBraidRing p))) p).left ≅
      pullback (scalarQuotientModel W p).hom (legendreBraidCover p) :=
  (Over.forget _).mapIso (coefficientScalarQuotientIso W (LegendreBraidRing p) p)

@[reassoc (attr := simp)]
theorem braidCyclicPullbackIso_fst :
    (braidCyclicPullbackIso p W).hom ≫
      pullback.fst (scalarQuotientModel W p).hom (legendreBraidCover p) =
        coefficientScalarQuotientMorphism W (LegendreBraidRing p) p :=
  coefficientScalarQuotientComparison_fst W (LegendreBraidRing p) p

instance braidCyclicCoverEffectiveEpi :
    EffectiveEpi (coefficientScalarQuotientMorphism W (LegendreBraidRing p) p) := by
  rw [← braidCyclicPullbackIso_fst]
  infer_instance

instance legendreBraidCyclicCoverEffectiveEpi : EffectiveEpi (legendreBraidCyclicCover p) :=
  braidCyclicCoverEffectiveEpi p (legendreModel p)

/-- Equality of cyclic maps can be tested on the common coefficient cover. -/
theorem braidCyclic_hom_ext {Y : Scheme}
    (f g : (scalarQuotientModel W p).left ⟶ Y)
    (h : coefficientScalarQuotientMorphism W (LegendreBraidRing p) p ≫ f =
      coefficientScalarQuotientMorphism W (LegendreBraidRing p) p ≫ g) : f = g :=
  (cancel_epi (coefficientScalarQuotientMorphism W (LegendreBraidRing p) p)).mp h

/-- Refinement from the common cyclic cover to the minus-one root cover. -/
def braidToSwapCyclic :
    (scalarQuotientModel (W.map (algebraMap (LegendreBase p) (LegendreBraidRing p))) p).left ⟶
      (scalarQuotientModel
        (W.map (algebraMap (LegendreBase p) (LegendreUniversalSwapRing p))) p).left :=
  coefficientCyclicMap W p
    (quadraticTripleFirstMap (-1) (legendreParameterUnit p) (legendreComplementUnit p))

/-- Refinement from the common cyclic cover to the parameter-root cover. -/
def braidToReciprocalCyclic :
    (scalarQuotientModel (W.map (algebraMap (LegendreBase p) (LegendreBraidRing p))) p).left ⟶
      (scalarQuotientModel
        (W.map (algebraMap (LegendreBase p) (LegendreUniversalReciprocalRing p))) p).left :=
  coefficientCyclicMap W p
    (quadraticTripleSecondMap (-1) (legendreParameterUnit p) (legendreComplementUnit p))

@[reassoc (attr := simp)]
theorem braidToSwapCyclic_coefficient :
    braidToSwapCyclic p W ≫ coefficientScalarQuotientMorphism W
      (LegendreUniversalSwapRing p) p =
        coefficientScalarQuotientMorphism W (LegendreBraidRing p) p :=
  coefficientCyclicMap_coefficient W p _

@[reassoc (attr := simp)]
theorem braidToReciprocalCyclic_coefficient :
    braidToReciprocalCyclic p W ≫ coefficientScalarQuotientMorphism W
      (LegendreUniversalReciprocalRing p) p =
        coefficientScalarQuotientMorphism W (LegendreBraidRing p) p :=
  coefficientCyclicMap_coefficient W p _



/-- Refinement from the common cyclic cover to the complementary-root cover. -/
def braidToComplementCyclic :
    (scalarQuotientModel (W.map (algebraMap (LegendreBase p) (LegendreBraidRing p))) p).left ⟶
      (scalarQuotientModel
        (W.map (algebraMap (LegendreBase p) (QuadraticEtaleRing (legendreComplementUnit p))))
          p).left :=
  coefficientCyclicMap W p
    (quadraticTripleThirdMap (-1) (legendreParameterUnit p) (legendreComplementUnit p))

@[reassoc (attr := simp)]
theorem braidToComplementCyclic_coefficient :
    braidToComplementCyclic p W ≫ coefficientScalarQuotientMorphism W
      (QuadraticEtaleRing (legendreComplementUnit p)) p =
        coefficientScalarQuotientMorphism W (LegendreBraidRing p) p :=
  coefficientCyclicMap_coefficient W p _

variable (d : (LegendreBase p)ˣ)
variable [IsNoetherianRing (QuadraticEtaleRing d)] [IsDomain (QuadraticEtaleRing d)]
variable [Fact (IsUnit (p : QuadraticEtaleRing d))]
variable (V : WeierstrassCurve (LegendreBase p)) [V.IsElliptic]

/-- A descended quadratic coordinate map pulls back to its actual common-cover transport. -/
@[reassoc]
theorem quadraticCoordinateDesc_braid_fac
    (σ : QuadraticEtaleRing d →ₐ[LegendreBase p] LegendreBraidRing p)
    (ha₁ : W.a₁ = 0) (ha₃ : W.a₃ = 0) (r : LegendreBase p)
    (h : signCoordinateChange (quadraticEtaleUnit d)
      (algebraMap (LegendreBase p) (QuadraticEtaleRing d) r) •
        W.map (algebraMap (LegendreBase p) (QuadraticEtaleRing d)) =
          V.map (algebraMap (LegendreBase p) (QuadraticEtaleRing d))) :
    coefficientScalarQuotientMorphism V (LegendreBraidRing p) p ≫
      quadraticCoordinateDesc W p d V ha₁ ha₃ r h =
        (groupCyclicParameterIso p (variableChangeCongrOverIso
          (W.map (algebraMap (LegendreBase p) (LegendreBraidRing p)))
          (V.map (algebraMap (LegendreBase p) (LegendreBraidRing p)))
          ((signCoordinateChange (quadraticEtaleUnit d)
            (algebraMap (LegendreBase p) (QuadraticEtaleRing d) r)).map σ.toRingHom)
          (coefficientCompare_variableChange_equation W σ V _ h))).hom.left ≫
            coefficientScalarQuotientMorphism W (LegendreBraidRing p) p := by
  rw [← coefficientCyclicMap_coefficient V p σ, Category.assoc, quadraticCoordinateDesc_fac,
    ← Category.assoc, coefficientCompare_variableChange_cyclic, Category.assoc,
    coefficientCyclicMap_coefficient]


end WeierstrassCurve.CubicCharts
