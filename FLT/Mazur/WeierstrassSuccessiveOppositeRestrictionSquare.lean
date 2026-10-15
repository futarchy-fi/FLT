/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveNodeRestrictionSquare
public import FLT.Mazur.SuccessiveIncidencePolygonRestriction
public import FLT.Mazur.WeierstrassSuccessiveOppositeNodeChart

/-!
# The opposite original branch commutes with coefficient restriction

The opposite slope is obtained from the small slope and the linear
coefficient. Hence both opens of the original branch cover restrict naturally.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory
namespace FLT.Mazur.WeierstrassSuccessiveX
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (R S : Type u) [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (I : Ideal R) (hI : IsNilpotent I) (J : Ideal S) (hJ : IsNilpotent J)
  (hf : I ≤ J.comap (algebraMap R S)) (ha : IsUnit W.a₁) (hs : s ∈ I) (h2 : W.a₂ ∈ I)
  (h3 : b3 ∈ I) (h4 : b4 ∈ I) (h6 : b6 ∈ I)
local notation "f" => algebraMap R S
local notation "F" => SuccessiveIncidence.coefficientRingMap f π
local notation "v" => oppositeNodeSlope W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "v'" => oppositeNodeSlope (W.map f) (f s) (f π) (f b3) (f b4) (f b6)
  J hJ (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)
local notation "hv" => oppositeNodeSlope_equation W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6
local notation "hv'" => oppositeNodeSlope_equation (W.map f) (f s) (f π) (f b3) (f b4)
  (f b6) J hJ (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6)

/-- The opposite slope retains its specified branch under coefficient restriction. -/
theorem oppositeNodeSlope_map : F v = v' := by
  simp only [oppositeNodeSlope, QuadraticRootBranchLocalization.oppositeRoot,
    map_sub, map_neg, nodeSlopeLinear_map,
    nilpotentNodeSlope_map f W s π b3 b4 b6 I hI J hJ hf ha hs h2 h3 h4 h6]

/-- Evaluation on the opposite branch commutes with restriction on all coordinates. -/
theorem oppositeNodeRetraction_map :
    (F).comp (simpleSlopeRetraction W s π b3 b4 b6 v hv).toRingHom =
      (simpleSlopeRetraction (W.map f) (f s) (f π) (f b3) (f b4) (f b6) v' hv').toRingHom.comp
        (coefficientRingMap f W s π b3 b4 b6) := by
  apply coefficient_ringHom_ext
  · intro r
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgHom.commutes, coefficientRingMap_algebraMap,
      SuccessiveIncidence.coefficientRingMap_algebraMap]
  · intro i
    simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      coefficientRingMap_coord, simpleSlopeRetraction_coord]
    fin_cases i
    · exact SuccessiveIncidence.coefficientRingMap_t f π
    · exact oppositeNodeSlope_map R S W s π b3 b4 b6 I hI J hJ hf ha hs h2 h3 h4 h6
    · exact SuccessiveIncidence.coefficientRingMap_u f π

/-- The opposite polygon open commutes with the original tensor coefficient projection. -/
@[reassoc] theorem oppositePolygonChart_restriction_square :
    PolygonSmoothing.chartCoefficient R S π ≫
      oppositePolygonChart W s π b3 b4 b6 I hI ha hs h2 h3 h4 h6 =
    oppositePolygonChart (W.map f) (f s) (f π) (f b3) (f b4) (f b6) J hJ
      (ha.map f) (hf hs) (hf h2) (hf h3) (hf h4) (hf h6) ≫
        Spec.map (CommRingCat.ofHom (coefficientRingMap f W s π b3 b4 b6)) := by
  simp only [oppositePolygonChart, simpleSlopePolygonChart, ← Category.assoc]
  rw [SuccessiveIncidence.toPolygon_restriction_square]
  simp only [Category.assoc]
  congr 1
  simp only [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  exact congrArg (fun g => Spec.map (CommRingCat.ofHom g))
    (oppositeNodeRetraction_map R S W s π b3 b4 b6 I hI J hJ hf ha hs h2 h3 h4 h6)

end FLT.Mazur.WeierstrassSuccessiveX
