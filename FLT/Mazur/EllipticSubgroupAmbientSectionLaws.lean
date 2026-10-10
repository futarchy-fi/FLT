/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticSubgroupClosureNegation
public import FLT.Mazur.WeierstrassProjectiveGroupComparison
public import FLT.Mazur.WeierstrassIntegralSeparated

/-!
# The integral subgroup sections retain the ambient group law

Separatedness over the valuation ring extends the generic point identities
to the original integral sections. Addition uses the proved good-reduction law.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits CartesianMonoidalCategory

namespace FLT.Mazur.EllipticSubgroupChart

open WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {K : Type*} [Field K] (A : ValuationSubring K) (W : WeierstrassCurve A)
  (H : AddSubgroup (W.map (algebraMap A K)).toProjective.Point)

/-- Integral ambient morphisms over the same base map are determined by their generic points. -/
theorem ambientSections_generic_ext (f g : Spec (.of A) ⟶ integralCurve W)
    (hb : f ≫ integralCurveStructure W = g ≫ integralCurveStructure W)
    (h : Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ g) : f = g := by
  let _ : IsDominant (Spec.map (CommRingCat.ofHom (algebraMap A K))) :=
    ⟨valuationGeneric_denseRange A⟩
  exact ext_of_isDominant_of_isSeparated (integralCurveStructure W) hb _ h

/-- The closure's integral zero section is the original cubic infinity section. -/
theorem integralSection_zero_toCurve :
    integralSection A W H 0 ≫ closureToCurve A W H 1 2 = integralCurveZero W := by
  apply ambientSections_generic_ext A W
  · rw [Category.assoc, closureToCurve_structure, integralSection_toBase,
      integralCurveZero_structure]
  · rw [integralSection_generic_toCurve]
    exact projectiveToIntegral_zero W

/-- The actual pair of ambient integral sections lies over the common base. -/
def ambientSectionPair (P Q : H) : Spec (.of A) ⟶ integralCurveProduct W :=
  pullback.lift (integralSection A W H P ≫ closureToCurve A W H 1 2)
    (integralSection A W H Q ≫ closureToCurve A W H 1 2) (by
      simp only [Category.assoc, closureToCurve_structure, integralSection_toBase])

/-- The first projection of the integral pair is the prescribed first section. -/
@[reassoc] theorem ambientSectionPair_fst (P Q : H) :
    ambientSectionPair A W H P Q ≫ pullback.fst _ _ =
      integralSection A W H P ≫ closureToCurve A W H 1 2 := pullback.lift_fst _ _ _

/-- The second projection of the integral pair is the prescribed second section. -/
@[reassoc] theorem ambientSectionPair_snd (P Q : H) :
    ambientSectionPair A W H P Q ≫ pullback.snd _ _ =
      integralSection A W H Q ≫ closureToCurve A W H 1 2 := pullback.lift_snd _ _ _

/-- The integral pair extends the actual pair of generic projective points. -/
theorem ambientSectionPair_generic (P Q : H) :
    Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ ambientSectionPair A W H P Q =
      (lift (projectiveToIntegral W P.1) (projectiveToIntegral W Q.1)).left := by
  apply pullback.hom_ext
  · rw [Category.assoc, ambientSectionPair_fst, integralSection_generic_toCurve,
      Over.lift_left]
    exact (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, ambientSectionPair_snd, integralSection_generic_toCurve,
      Over.lift_left]
    exact (pullback.lift_snd _ _ _).symm

/-- Good-reduction addition of the actual integral sections stays in the subgroup sections. -/
theorem ambientSectionPair_addition (hΔ : IsUnit W.Δ) (P Q : H) :
    ambientSectionPair A W H P Q ≫ integralCurveAddition W hΔ =
      integralSection A W H (P + Q) ≫ closureToCurve A W H 1 2 := by
  apply ambientSections_generic_ext A W
  · rw [Category.assoc, integralCurveAddition_structure, ← Category.assoc,
      ambientSectionPair_fst, Category.assoc, closureToCurve_structure,
      integralSection_toBase, Category.assoc, closureToCurve_structure, integralSection_toBase]
  · rw [← Category.assoc, ambientSectionPair_generic, integralSection_generic_toCurve]
    exact (congrArg Over.Hom.left (projectiveToIntegral_add W hΔ P.1 Q.1)).symm

end FLT.Mazur.EllipticSubgroupChart
