/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassVariableChangeSmoothProduct
public import FLT.Mazur.WeierstrassVariableChangeAddition
public import FLT.Mazur.WeierstrassSmoothCoefficientAddition

/-!
# Variable changes preserve smooth addition on singular fibers

The actual secant formulas commute with the proper variable change. Flat
secant descent extends the equality to the full smooth product over an
arbitrary coefficient ring, without assuming the discriminant is a unit.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits WeierstrassCurve
namespace FLT.Mazur.WeierstrassIntegralChart
open WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] (W V : WeierstrassCurve R)
  (C : VariableChange R) (h : C • W = V)
local notation "e" => integralVariableChangeSmoothMap W V C h
local notation "E" => integralVariableChangeIso W V C h
local notation "P" => integralVariableChangeSmoothProduct W V C h

/-- The actual secant presentation retains both original proper inputs. -/
@[reassoc] theorem secantVariableChange_globalDomain :
    Spec.map (CommRingCat.ofHom (secantVariableChange W V C h).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (secantRestriction W).toRingHom) ≫
          integralCurveProductChart W false false =
      (Spec.map (CommRingCat.ofHom (secantRestriction V).toRingHom) ≫
        integralCurveProductChart V false false) ≫ integralVariableChangeProduct W V C h := by
  rw [Category.assoc, integralVariableChangeProduct_affine]
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ integralCurveProductChart W false false)
      (secantVariableChange_spec_restriction W V C h).symm).trans
        (Category.assoc _ _ _))

/-- The full smooth law commutes with every integral variable change, including bad fibers. -/
@[reassoc] theorem integralVariableChangeSmoothMap_addition :
    smoothFactorAddition V ≫ e = P ≫ smoothFactorAddition W := by
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  let _ : Flat (smoothFactorsInclusion V) := by
    rw [← smoothFactorsToProduct_inclusion]
    let _ : IsIso (smoothFactorsToProduct V) := (smoothProductFactorsIso V).symm.isIso_hom
    infer_instance
  apply flatProduct_hom_ext_secant V (smoothFactorsInclusion V) (integralCurveStructure W)
  · simp only [Category.assoc, integralVariableChangeSmoothMap_inclusion]
    change smoothFactorAddition V ≫ (integralSmoothOpen V).ι ≫
        (E).hom ≫ integralCurveStructure W = P ≫ smoothFactorAddition W ≫
          integralSmoothStructure W
    rw [show (E).hom ≫ integralCurveStructure W = integralCurveStructure V from
      integralVariableChangeTo_structure W V C h]
    change smoothFactorAddition V ≫ integralSmoothStructure V = _
    rw [smoothFactorAddition_structure, smoothFactorAddition_structure,
      integralVariableChangeSmoothProduct_fst_assoc, integralVariableChangeSmoothMap_structure]
  · intro U p a ha
    have hl := smoothFactorAddition_secant V p a ha
    have hr := smoothFactorAddition_secant W (p ≫ P)
      (a ≫ Spec.map (CommRingCat.ofHom (secantVariableChange W V C h).toRingHom)) (by
        rw [Category.assoc, secantVariableChange_globalDomain, ← Category.assoc, ha]
        simp only [Category.assoc, integralVariableChangeSmoothProduct_inclusion])
    simp only [Category.assoc, integralVariableChangeSmoothMap_inclusion]
    rw [← Category.assoc (smoothFactorAddition V), ← Category.assoc p, hl, Category.assoc,
      Category.assoc, integralVariableChangeIso_affine]
    rw [← Category.assoc p, hr]
    simp only [← Category.assoc]
    apply congrArg (· ≫ integralCurveChart W 2)
    simp only [Category.assoc]
    apply congrArg (a ≫ ·)
    change Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact congrArg AlgHom.toRingHom (secantVariableChange_addition W V C h).symm

end FLT.Mazur.WeierstrassIntegralChart
