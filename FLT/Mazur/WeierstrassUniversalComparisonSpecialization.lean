/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedComparisonPullbackCoherence
public import FLT.Mazur.WeierstrassCoefficientModelComposition
public import FLT.Mazur.WeierstrassChangeGeneralizedNaturality

/-!
# Specialization of the actual universal full comparison

The pullback of the universal generalized-curve isomorphism is the full change
extracted from its algebra parameter. This identifies actual morphisms rather
than inferring naturality from the existence of a pointwise bijection.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficientPresentationIso coefficientModelIso changeGeneralizedIso

/-- Equal composite coefficient maps retain the full tower coherence. -/
theorem coefficientPresentation_comp_eq {R Q A : Type}
    [CommRing R] [CommRing Q] [CommRing A]
    (W : WeierstrassCurve R) (V : WeierstrassCurve Q) (Z : WeierstrassCurve A)
    (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) (hZ : IsUnit Z.Δ)
    (f : R →+* Q) (g : Q →+* A) (t : R →+* A) (ht : t = g.comp f)
    (hf : V = W.map f) (hg : Z = V.map g) (hz : Z = W.map t) :
    (coefficientPresentationIso W hW t Z hZ hz).hom ≫
      ((integralGeneralizedEllipticCurve W hW).baseChangeCompEqIso
        (Spec.map (CommRingCat.ofHom f)) (Spec.map (CommRingCat.ofHom g))
        (Spec.map (CommRingCat.ofHom t))
        (by rw [ht]; exact Spec.map_comp _ _)).hom =
      (coefficientPresentationIso V hV g Z hZ hg).hom ≫
        baseChangeMap (Spec.map (CommRingCat.ofHom g))
          (coefficientPresentationIso W hW f V hV hf).hom := by
  subst t
  exact coefficientPresentationIso_comp W V Z hW hV hZ f g hf hg hz

variable {R A : Type} [CommRing R] [CommRing A] [Algebra R A]
  (W V : WeierstrassCurve R) (hW : IsUnit W.Δ) (hV : IsUnit V.Δ)
  (p : EquationRing W V →ₐ[R] A)
local notation "Q" => EquationRing W V
local notation "s" => Spec.algebraMap R Q
local notation "t" => Spec.algebraMap R A
local notation "k" => Spec.map (CommRingCat.ofHom p.toRingHom)

/-- The actual parameter map lies over the prescribed original coefficient base. -/
theorem universalComparisonTest_base : t = k ≫ s := by
  rw [← Spec.map_comp]
  exact congrArg Spec.map (CommRingCat.hom_ext p.comp_algebraMap.symm)

/-- The actual universal comparison restricted to an affine algebra test. -/
def universalComparisonOnAlgebra :
    (integralGeneralizedEllipticCurve W hW).baseChange t ≅
      (integralGeneralizedEllipticCurve V hV).baseChange t :=
  comparisonPullback _ _ s k t (universalComparisonTest_base W V p)
    (universalGeneralizedComparison W V hW hV)

/-- Pulling back the universal full comparison gives exactly the extracted admissible change. -/
theorem universalComparisonOnAlgebra_eq :
    universalComparisonOnAlgebra W V hW hV p =
      changeBaseGeneralizedIso W V hW hV ((equationChange W V).map p.toRingHom)
        (equationChange_map_equation W V p) := by
  let _ : Algebra Q A := p.toAlgebra
  have hm (U : WeierstrassCurve R) :
      U.map (algebraMap R A) = (U.map (algebraMap R Q)).map p.toRingHom := by
    rw [WeierstrassCurve.map_map]
    exact congrArg U.map p.comp_algebraMap.symm
  let a := coefficientPresentationIso (W.map (algebraMap R Q))
    (coefficientEquation_discriminant W hW _) p.toRingHom (W.map (algebraMap R A))
    (coefficientEquation_discriminant W hW _) (hm W)
  let b := coefficientPresentationIso (V.map (algebraMap R Q))
    (coefficientEquation_discriminant V hV _) p.toRingHom (V.map (algebraMap R A))
    (coefficientEquation_discriminant V hV _) (hm V)
  rw [universalComparisonOnAlgebra, universalGeneralizedComparison,
    changeBaseGeneralizedIso_eq, changeBaseGeneralizedIso_eq]
  apply comparisonPullback_conjugate (r := a) (q := b)
  · have hc := coefficientPresentation_comp_eq W _ _ hW
      (coefficientEquation_discriminant W hW (algebraMap R Q))
      (coefficientEquation_discriminant W hW (algebraMap R A))
      (algebraMap R Q) p.toRingHom (algebraMap R A) p.comp_algebraMap.symm
      rfl (hm W) rfl
    simpa only [a, coefficientPresentationIso, eqToIso_refl, Iso.refl_trans] using hc
  · have hc := coefficientPresentation_comp_eq V _ _ hV
      (coefficientEquation_discriminant V hV (algebraMap R Q))
      (coefficientEquation_discriminant V hV (algebraMap R A))
      (algebraMap R Q) p.toRingHom (algebraMap R A) p.comp_algebraMap.symm
      rfl (hm V) rfl
    simpa only [b, coefficientPresentationIso, eqToIso_refl, Iso.refl_trans] using hc
  · exact changePresentationIso_natural (W.map (algebraMap R Q)) (V.map (algebraMap R Q))
      (coefficientEquation_discriminant W hW _) (coefficientEquation_discriminant V hV _)
      (equationChange W V) (equationChange_equation W V)
      (W.map (algebraMap R A)) (V.map (algebraMap R A)) _ _ (hm W) (hm V)
      ((equationChange W V).map p.toRingHom) rfl (equationChange_map_equation W V p)

end FLT.Mazur.WeierstrassChangeParameter
