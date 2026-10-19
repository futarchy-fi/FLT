/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassUniversalComparisonRingHom
public import FLT.Mazur.WeierstrassComparisonCoefficientHom

/-!
# Full universal comparisons under coefficient refinement

The actual comparison coefficient morphism pulls back the full universal
comparison to the refined one, with the original model presentations retained.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry WeierstrassCurve
namespace FLT.Mazur.WeierstrassChangeParameter
open WeierstrassIntegralChart GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] coefficientPresentationIso coefficientModelIso
  comparisonPresentationHom
variable {R A : Type} [CommRing R] [CommRing A]
  (W V : WeierstrassCurve R) (W' V' : WeierstrassCurve A)
  (hW : IsUnit W.Δ) (hV : IsUnit V.Δ) (hW' : IsUnit W'.Δ) (hV' : IsUnit V'.Δ)
  (f : R →+* A) (hw : W' = W.map f) (hv : V' = V.map f)
local notation "Q'" => EquationRing W' V'
local notation "p" => comparisonPresentationHom W V W' V' f hw hv
local notation "k" => Spec.map (CommRingCat.ofHom f)
local notation "s'" => comparisonStructure W' V'
local notation "t" => RingHom.comp (algebraMap A Q') f
local notation "kt" => Spec.map (CommRingCat.ofHom t)
local notation "hs" => Spec.map_comp (CommRingCat.ofHom f)
  (CommRingCat.ofHom (algebraMap A Q'))
local notation "E" => integralGeneralizedEllipticCurve W hW
local notation "F" => integralGeneralizedEllipticCurve V hV

/-- The overlap coefficient map retains the actual universal full comparison. -/
theorem universalGeneralizedComparison_refine :
    comparisonPullback E F (comparisonStructure W V) (Spec.map (CommRingCat.ofHom p)) kt
      ((congrArg (fun z ↦ Spec.map (CommRingCat.ofHom z))
        (comparisonPresentationHom_base W V W' V' f hw hv).symm).trans
          (Spec.map_comp (CommRingCat.ofHom (algebraMap R (EquationRing W V)))
            (CommRingCat.ofHom p)))
      (universalGeneralizedComparison W V hW hV) =
    (E).baseChangeCompEqIso k s' kt hs ≪≫
      ((baseChangeFunctor s').mapIso (coefficientPresentationIso W hW f W' hW' hw)).symm ≪≫
        universalGeneralizedComparison W' V' hW' hV' ≪≫
          (baseChangeFunctor s').mapIso (coefficientPresentationIso V hV f V' hV' hv) ≪≫
            ((F).baseChangeCompEqIso k s' kt hs).symm := by
  have heq (U : WeierstrassCurve R) (U' : WeierstrassCurve A) (hu : U' = U.map f) :
      U'.map (algebraMap A Q') = U.map t := by
    rw [hu, WeierstrassCurve.map_map]
  let c := coefficientPresentationIso W hW t (W'.map (algebraMap A Q'))
    (coefficientEquation_discriminant W' hW' _) (heq W W' hw)
  let d := coefficientPresentationIso V hV t (V'.map (algebraMap A Q'))
    (coefficientEquation_discriminant V' hV' _) (heq V V' hv)
  have hc : c = coefficientModelIso W' hW' (algebraMap A Q') ≪≫
      (baseChangeFunctor s').mapIso (coefficientPresentationIso W hW f W' hW' hw) ≪≫
        ((E).baseChangeCompEqIso k s' kt hs).symm := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
    apply (Iso.eq_comp_inv _).mpr
    simpa only [c, coefficientPresentationIso, eqToIso_refl, Iso.refl_trans,
      comparisonStructure, Spec.algebraMap, Functor.mapIso_hom, baseChangeFunctor] using
      coefficientPresentationIso_comp W W' _ hW hW'
        (coefficientEquation_discriminant W' hW' _) f (algebraMap A Q') hw rfl (heq W W' hw)
  have hd : d = coefficientModelIso V' hV' (algebraMap A Q') ≪≫
      (baseChangeFunctor s').mapIso (coefficientPresentationIso V hV f V' hV' hv) ≪≫
        ((F).baseChangeCompEqIso k s' kt hs).symm := by
    apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, ← Category.assoc]
    apply (Iso.eq_comp_inv _).mpr
    simpa only [d, coefficientPresentationIso, eqToIso_refl, Iso.refl_trans,
      comparisonStructure, Spec.algebraMap, Functor.mapIso_hom, baseChangeFunctor] using
      coefficientPresentationIso_comp V V' _ hV hV'
        (coefficientEquation_discriminant V' hV' _) f (algebraMap A Q') hv rfl (heq V V' hv)
  rw [universalComparisonOnRingHom_eq W V hW hV p t
    (comparisonPresentationHom_base W V W' V' f hw hv).symm
    _ _ _ _ (heq W W' hw) (heq V V' hv) (equationChange W' V')
    (comparisonPresentationHom_change W V W' V' f hw hv).symm
    (equationChange_equation W' V')]
  change c.symm ≪≫ _ ≪≫ d = _
  rw [hc, hd, universalGeneralizedComparison, changeBaseGeneralizedIso_eq]
  apply Iso.ext
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv, Category.assoc]

end FLT.Mazur.WeierstrassChangeParameter
