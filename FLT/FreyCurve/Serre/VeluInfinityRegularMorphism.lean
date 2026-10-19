/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.FreyCurve.Serre.VeluInfinityTargetGeneric
public import FLT.FreyCurve.Serre.VeluGenericChartMorphism

/-!
# The original Vélu map extends regularly through source infinity

The iterated principal neighborhood embeds into the actual source cubic. The
regular chart map defines a morphism to the actual target, taking infinity to infinity.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry FLT.Mazur.WeierstrassIntegralChart

namespace WeierstrassCurve.Velu

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

attribute [local irreducible] infinityTargetCoordinates infinityTargetHom

variable {K : Type} [Field K] [CharZero K] [DecidableEq K]
  (E : WeierstrassCurve K) (G : AddSubgroup E.toAffine.Point) [Fintype G]

/-- The explicit iterated principal neighborhood in the original source cubic. -/
def veluInfinityOpenImmersion : Spec (.of (InfinityTargetRing E G)) ⟶ integralCurve E :=
  Spec.map (CommRingCat.ofHom (algebraMap (InfinityKernelRing E G) (InfinityTargetRing E G))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (InfinityParameterRing E) (InfinityKernelRing E G))) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (Coordinate E 1) (InfinityParameterRing E))) ≫
    integralCurveChart E 1

/-- This is an actual open subscheme of the source, not just a formal neighborhood. -/
instance veluInfinityOpenImmersion_isOpenImmersion :
    IsOpenImmersion (veluInfinityOpenImmersion E G) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _ ≫ _ ≫ integralCurveChart E 1))

/-- The actual source infinity point lifts to the constructed neighborhood. -/
def veluInfinityPointLift : Spec (.of K) ⟶ Spec (.of (InfinityTargetRing E G)) :=
  Spec.map (CommRingCat.ofHom (infinityTargetEvaluation E G).toRingHom)

/-- The lift retains the original infinity point of the source cubic. -/
@[reassoc] theorem veluInfinityPointLift_source :
    veluInfinityPointLift E G ≫ veluInfinityOpenImmersion E G =
      Spec.map (CommRingCat.ofHom (infinityEvaluation E).toRingHom) ≫
        integralCurveChart E 1 := by
  simp only [veluInfinityPointLift, veluInfinityOpenImmersion, ← Spec.map_comp_assoc]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (infinityTargetEvaluation_algebraMap E G _).trans
    ((infinityKernelEvaluation_algebraMap E G _).trans
      (infinityParameterEvaluation_algebraMap E a))

variable (hodd : ∀ Q : G, Q ≠ 0 → Q ≠ -Q)

/-- The regular extension through infinity into the actual glued target cubic. -/
def veluInfinityRegularMorphism :
    Spec (.of (InfinityTargetRing E G)) ⟶ integralCurve (curve E G) :=
  Spec.map (CommRingCat.ofHom (infinityTargetChart E G hodd).toRingHom) ≫
    integralCurveChart (curve E G) 1

/-- The regular extension preserves the original coefficient field. -/
@[reassoc] theorem veluInfinityRegularMorphism_base :
    veluInfinityRegularMorphism E G hodd ≫ integralCurveStructure (curve E G) =
      Spec.map (CommRingCat.ofHom (algebraMap K (InfinityTargetRing E G))) := by
  rw [veluInfinityRegularMorphism, Category.assoc, integralCurveChart_structure]
  exact specAlgHom_structure _

/-- The actual morphism takes original source infinity to original target infinity. -/
@[reassoc] theorem veluInfinityRegularMorphism_point :
    veluInfinityPointLift E G ≫ veluInfinityRegularMorphism E G hodd =
      Spec.map (CommRingCat.ofHom (infinityEvaluation (curve E G)).toRingHom) ≫
        integralCurveChart (curve E G) 1 := by
  rw [veluInfinityPointLift, veluInfinityRegularMorphism, ← Spec.map_comp_assoc]
  have h : (infinityTargetEvaluation E G).comp (infinityTargetChart E G hodd) =
      infinityEvaluation (curve E G) := by
    apply hom_ext
    intro i
    change infinityTargetEvaluation E G
      (infinityTargetChart E G hodd (coord (curve E G) 1 i)) = _
    rw [infinityTargetChart, evaluation_coord, infinityTargetCoordinates_value]
    exact (evaluation_coord _ _ _ _ _ _).symm
  change Spec.map (CommRingCat.ofHom
    ((infinityTargetEvaluation E G).comp (infinityTargetChart E G hodd)).toRingHom) ≫ _ = _
  rw [h]

end WeierstrassCurve.Velu
