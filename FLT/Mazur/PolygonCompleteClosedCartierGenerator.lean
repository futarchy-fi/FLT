/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteClosedFiniteSubgroup
public import FLT.Mazur.GeneralizedCurveAmpleSubgroup

/-!
# Cyclicity and ampleness of the original closed complete divisor

The generator lies in the original pulled-back product divisor. Its powers
recover the original marked sections as scheme morphisms, so their sum is an
equality of Cartier ideals. The known polygon cubic embedding proves ampleness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching GeneralizedEllipticCurve
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] completeClosedPolygon_lfp cyclic_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "S" => Spec (CommRingCat.of K)
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "b" => completeClosedBase K
local notation "j" => completeClosedFiberInclusion K n h
local notation "q" => PolygonCyclicAtlas.toBase K n h
local notation "hb" => completeClosedFiber_isPullback K n h

/-- The original complete product ideal restricts to the all-one polygon ideal. -/
theorem completeMarkingDivisor_closed :
    (completeMarkingDivisor K n h).comap j =
      PolygonBoundaryDivisor.ideal K n P (fun _ ↦ 1) := by
  simp only [completeMarkingDivisor, FCurve.idealSheaf_comap_prod,
    completeBaseMarking_ker_closed]
  rfl

/-- The original closed subgroup is relatively Cartier. -/
theorem completeClosedFiniteSubgroup_relativeCartier :
    FCurve.RelativeEffectiveCartier (PolygonCyclicAtlas.polygon K n h).hom
      (completeClosedFiniteSubgroup K n h).ideal := by
  rw [completeClosedFiniteSubgroup_ideal, completeMarkingDivisor_closed]
  exact PolygonBoundaryDivisor.cartier K n P hn Q hp (fun _ ↦ 1)

/-- The generator is a section of the original closed complete divisor. -/
def completeClosedGenerator : 𝟙_ (Over S) ⟶ (completeClosedFiniteSubgroup K n h).carrier :=
  ConstantCyclicGroup.component S n 1 ≫ (completeCyclicDivisorIso K n h b j q hb).hom

/-- Each generator power recovers the original complete Cartesian marked section. -/
theorem completeClosedGenerator_orbit (i : Fin n) :
    ((completeClosedGenerator K n h ^ i.val) ≫
        (completeClosedFiniteSubgroup K n h).curveMap).left =
      completeCartesianMarking K n h b j q hb i := by
  let _ := completeCyclicDivisorCommGrpObj K n h b j q hb
  have : IsMonHom (completeCyclicDivisorIso K n h b j q hb).hom := by infer_instance
  rw [completeClosedGenerator, ← MonObj.pow_comp, Over.comp_left,
    completeClosedFiniteSubgroup_curveMap, Over.comp_left, Category.assoc]
  rw [show (completeCyclicDivisorIso K n h b j q hb).hom.left =
      (completeCyclicDivisorSchemeIso K n h b j q hb).hom from rfl,
    completeCyclicDivisorSchemeIso_ι, ← ConstantCyclicGenerator.component_pow]
  change ((ConstantCyclicGroup.component S n (ZMod.finEquiv n i)) ≫
    completeCyclicMarking K n h b j q hb).left = _
  rw [show ConstantCyclicGroup.component S n (ZMod.finEquiv n i) ≫
      completeCyclicMarking K n h b j q hb = _ from Sigma.ι_comp_desc _ _]
  simp only [completeCyclicSection, Over.homMk_left, RingEquiv.symm_apply_apply]

/-- The powers sum to the original ideal, including their scheme-theoretic multiplicities. -/
theorem completeClosedGenerator_isCartierGenerator :
    (completeClosedFiniteSubgroup K n h).IsCartierGenerator (completeClosedGenerator K n h) := by
  let _ := completeCyclicDivisorCommGrpObj K n h b j q hb
  have : IsMonHom (completeCyclicDivisorIso K n h b j q hb).hom := by infer_instance
  refine ⟨?_, completeClosedFiniteSubgroup_relativeCartier K n h, ?_⟩
  · rw [completeClosedGenerator, ← MonObj.pow_comp, ← ConstantCyclicGenerator.component_natCast,
      ZMod.natCast_self, ConstantCyclicGenerator.component_zero, MonObj.one_comp]
  · simp only [completeClosedFiniteSubgroup_ideal, completeMarkingDivisor,
      FCurve.idealSheaf_comap_prod, completeCartesianMarking_ker K n h b j q hb,
      completeClosedGenerator_orbit]

/-- The original complete closed subgroup is cyclic for the fppf topology. -/
theorem completeClosedFiniteSubgroup_isCyclic :
    (completeClosedFiniteSubgroup K n h).IsCyclic :=
  (completeClosedGenerator_isCartierGenerator K n h).isCyclic _

/-- The original subgroup divisor is ample, witnessed by the polygon cubic embedding. -/
theorem completeClosedFiniteSubgroup_isAmple :
    (completeClosedFiniteSubgroup K n h).IsAmple := by
  refine ⟨(completeClosedFiniteSubgroup_relativeCartier K n h).1,
    FCurve.RelativeAmple.of_power (by decide : 0 < 3) ?_⟩
  simpa only [completeClosedFiniteSubgroup_ideal, completeMarkingDivisor_closed,
    PolygonGeneralizedCurve.curve] using
      PolygonCubicSections.divisor_tensorCube_relativeVeryAmple K n hn P Q hp (fun _ ↦ 1)

end FLT.Mazur.PolygonInfinitesimalStages
