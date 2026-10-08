/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothFormulaComparison
public import FLT.Mazur.WeierstrassSplitNodalPartialSmoothMultiplication
public import FLT.Mazur.WeierstrassSmoothGroupOperations

/-!
# The constructed smooth law and nodal torus multiplication on original charts

The established ring-level nodal formulas identify both actual scheme
operations on every original affine-input addition domain.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Each original addition domain is over the same coefficient spectrum as its inputs. -/
theorem additionGlobalDomain_structure (i : AdditionChartIndex) :
    additionGlobalDomain W i ≫ pullback.fst _ _ ≫ integralCurveStructure W =
      Spec.map (CommRingCat.ofHom (algebraMap R (additionChartRing W i))) := by
  rw [additionGlobalDomain_fst_assoc, integralCurveChart_structure]
  unfold additionAffineInputLeft
  rw [Category.assoc, chartStructure, specAlgHom_structure]
  rw [additionChartInclusion.eq_def, ← additionChartAlgRestriction_toRingHom]
  cases i <;> exact specAlgHom_structure _

/-- The categorical smooth law retains the original chart morphism itself. -/
theorem smoothFactorAddition_originalChart {X : Scheme.{u}} (t : X ⟶ smoothFactorProduct W)
    (i : AdditionChartIndex) (f : X ⟶ Spec (additionChartRing W i))
    (hf : f ≫ additionGlobalDomain W i = t ≫ smoothFactorsInclusion W) :
    t ≫ smoothFactorAddition W ≫ (integralSmoothOpen W).ι = f ≫ additionCurveChart W i := by
  simpa only [additionCurveChart, additionChartAlgOutput_spec, Category.assoc] using
    smoothFactorAddition_chart W t i f hf

variable (a : Rˣ)

/-- The earlier transported torus multiplication as a morphism on the actual smooth pair. -/
irreducible_def splitNodalTransportedAddition : smoothFactorProduct (splitNodalEquation a) ⟶
    (integralSmoothOpen (splitNodalEquation a)).toScheme := by
  let _ := splitNodalSmoothCommGrpObj a
  exact (μ[splitNodalSmoothOver a]).left

/-- Pairing smooth points computes the same underlying transported operation. -/
theorem splitNodalTransportedAddition_pair {X : Scheme.{u}} (s : X ⟶ Spec (.of R))
    (v w : Over.mk s ⟶ splitNodalSmoothOver a) :
    let _ := splitNodalSmoothCommGrpObj a
    (lift v w).left ≫ splitNodalTransportedAddition a =
      (lift v w ≫ μ[splitNodalSmoothOver a]).left := by
  rw [splitNodalTransportedAddition_def]
  rfl

/-- Both smooth operations agree on any original addition chart of a smooth nodal pair. -/
theorem splitNodalSmoothAddition_chart {X : Scheme.{u}}
    (t : X ⟶ smoothFactorProduct (splitNodalEquation a)) (i : AdditionChartIndex)
    (f : X ⟶ Spec (additionChartRing (splitNodalEquation a) i))
    (hf : f ≫ additionGlobalDomain (splitNodalEquation a) i =
      t ≫ smoothFactorsInclusion (splitNodalEquation a)) :
    t ≫ smoothFactorAddition (splitNodalEquation a) = t ≫ splitNodalTransportedAddition a := by
  let W := splitNodalEquation a
  let s := t ≫ pullback.fst (integralSmoothStructure W) (integralSmoothStructure W) ≫
    integralSmoothStructure W
  let v : Over.mk s ⟶ splitNodalSmoothOver a := Over.homMk (t ≫ pullback.fst _ _) (by
    exact Category.assoc _ _ _)
  let w : Over.mk s ⟶ splitNodalSmoothOver a := Over.homMk (t ≫ pullback.snd _ _) (by
    change (t ≫ pullback.snd _ _) ≫ integralSmoothStructure W = s
    rw [Category.assoc, ← pullback.condition])
  have hp : (lift v w).left = t := by
    apply pullback.hom_ext <;> simp only [Over.lift_left, pullback.lift_fst, pullback.lift_snd]
    all_goals rfl
  have hb : f ≫ Spec.map (CommRingCat.ofHom (algebraMap R (additionChartRing W i))) = s := by
    rw [← additionGlobalDomain_structure W i, ← Category.assoc, hf]
    rw [Category.assoc, smoothFactorsInclusion_fst_assoc]
  have hl : (f ≫ Spec.map (CommRingCat.ofHom (additionInputLeft W i).toRingHom)) ≫
      integralCurveChart W 2 = v.left ≫ (integralSmoothOpen W).ι := by
    have hh := congrArg (fun k => k ≫ pullback.fst _ _) hf
    simp only [Category.assoc, additionGlobalDomain_fst, smoothFactorsInclusion_fst] at hh
    have hs : Spec.map (CommRingCat.ofHom (additionInputLeft W i).toRingHom) =
        additionAffineInputLeft W i := by
      change Spec.map (CommRingCat.ofHom ((additionChartAlgRestriction W i).toRingHom.comp
        (productLeft W).toRingHom)) = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, additionChartAlgRestriction_toRingHom]
      rfl
    rw [hs]
    simpa only [v, Over.homMk_left, Category.assoc] using hh
  have hr : (f ≫ Spec.map (CommRingCat.ofHom (additionInputRight W i).toRingHom)) ≫
      integralCurveChart W 2 = w.left ≫ (integralSmoothOpen W).ι := by
    have hh := congrArg (fun k => k ≫ pullback.snd _ _) hf
    simp only [Category.assoc, additionGlobalDomain_snd, smoothFactorsInclusion_snd] at hh
    have hs : Spec.map (CommRingCat.ofHom (additionInputRight W i).toRingHom) =
        additionAffineInputRight W i := by
      change Spec.map (CommRingCat.ofHom ((additionChartAlgRestriction W i).toRingHom.comp
        (productRight W).toRingHom)) = _
      rw [CommRingCat.ofHom_comp, Spec.map_comp, additionChartAlgRestriction_toRingHom]
      rfl
    rw [hs]
    simpa only [w, Over.homMk_left, Category.assoc] using hh
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [Category.assoc, smoothFactorAddition_originalChart W t i f hf]
  let _ := splitNodalSmoothCommGrpObj a
  have he := splitNodal_chart_smooth_multiplication a i s f v w hb hl hr
  dsimp only at he
  rw [← splitNodalTransportedAddition_pair, hp] at he
  exact he

end FLT.Mazur.WeierstrassIntegralChart
