/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PointedCubicSubgroupTransport
public import FLT.Mazur.CartierGeneratorMarkedSubgroup
public import FLT.Mazur.AuxiliaryLevelHomScheme

/-!
# Original Cartier generators in pointed cubic charts

The carrier and generator are retained, even when orbit sections coincide.
The homomorphism scheme records these sections without imposing faithfulness;
the original subgroup ideal is their product with all multiplicities.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open WeierstrassIntegralChart AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} [IsAffine S] [IsLocallyNoetherian S]
  {E : GeneralizedEllipticCurve S} {n : ℕ} [NeZero n] (H : E.FiniteSubgroup n)
  (W : WeierstrassCurve Γ(S, ⊤)) [W.IsElliptic]
  (e : E.curve.left ≅ integralCurve W)
  (he : e.hom ≫ integralCurveStructure W = E.curve.hom ≫ S.toSpecΓ)
  (hs : E.identitySection.left ≫ e.hom = S.toSpecΓ ≫ integralCurveZero W)
  {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

omit [NeZero n] in
include hP in
/-- The unchanged section generates the unchanged carrier in the full cubic chart. -/
theorem pointedCubicSubgroup_generator :
    (H.pointedCubicSubgroup W e he hs).IsCartierGenerator P := by
  simpa only [pointedCubicSubgroupIso, Iso.refl_hom, Category.comp_id] using
    (H.pointedCubicSubgroupIso W e he hs).cartierGenerator hP

/-- The actual original generator determines a point of the cyclic homomorphism scheme. -/
def pointedCubicCartierParameter : 𝟙_ (Over S) ⟶
    homScheme (pointedCubicFamily W).group (Multiplicative (ZMod n)) :=
  liftMarking _ _ ((H.pointedCubicSubgroup W e he hs).generatorCurveMarking
    (H.pointedCubicSubgroup_generator W e he hs hP))

/-- Every cyclic label is the original power followed by the full group comparison. -/
@[reassoc] theorem pointedCubicCartierParameter_value (i : Multiplicative (ZMod n)) :
    H.pointedCubicCartierParameter W e he hs hP ≫ value _ _ i =
      (H.generatorCurveMarking hP i) ≫ (pointedCubicFamilyIso W E e he hs).hom.group := by
  rw [pointedCubicCartierParameter, liftMarking_value]
  change (P ^ i.toAdd.val) ≫ (H.inclusion ≫ _) = ((P ^ i.toAdd.val) ≫ H.inclusion) ≫ _
  exact (Category.assoc _ _ _).symm

/-- Orbit-product equality retains multiplicities on the whole pointed cubic curve. -/
theorem pointedCubicCartierParameter_ideal :
    (H.pointedCubicSubgroup W e he hs).ideal = ∏ i : Fin n,
      ((H.pointedCubicCartierParameter W e he hs hP ≫
        value _ _ (Multiplicative.ofAdd (i.val : ZMod n))) ≫
          (pointedCubicFamily W).inclusion).left.ker := by
  rw [(H.pointedCubicSubgroup_generator W e he hs hP).2.2]
  apply Finset.prod_congr rfl
  intro i _
  rw [pointedCubicCartierParameter, liftMarking_value]
  change _ = (((H.pointedCubicSubgroup W e he hs).generatorPowers P
    (H.pointedCubicSubgroup_generator W e he hs hP).1 (.ofAdd (i.val : ZMod n)) ≫
      (H.pointedCubicSubgroup W e he hs).inclusion) ≫ _).left.ker
  rw [generatorPowers_natCast, Category.assoc]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
