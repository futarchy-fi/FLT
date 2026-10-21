/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCoefficientAmpleTower
public import FLT.Mazur.ArithmeticOneGonCoefficientSubgroupProjection
public import FLT.Mazur.CompatibleSubgroupPresentationExtension
public import FLT.Mazur.CompatibleSubgroupCurveProjectionExt

/-!
# The coefficient cocycle for full ample universal subgroups

Successive independent coefficient charts recover the direct full subgroup
comparison. The actual parameter-equality transport is retained, as are both
original coefficient comparisons and the canonical pullback comparison.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open CyclicBoundaryParameter GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (A B C : Type) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C]
  (t : A) (ht : IsUnit (1 + 432 * t)) (n : ℕ) [NeZero n]
local notation "E" => curve t ht
local notation "F" => curve (algebraMap A B t) (coefficientParameter_isUnit t ht)
local notation "G" => curve (algebraMap A C t) (coefficientParameter_isUnit t ht)
local notation "D" => curve (algebraMap B C (algebraMap A B t))
  (coefficientParameter_isUnit (S := C) (algebraMap A B t)
    (coefficientParameter_isUnit (S := B) t ht))
local notation "e" => parameterIso (IsScalarTower.algebraMap_apply A B C t)
  (coefficientParameter_isUnit (S := C) t ht)
  (coefficientParameter_isUnit (S := C) (algebraMap A B t)
    (coefficientParameter_isUnit (S := B) t ht))
local notation "p" => coefficientAmpleToOriginal (S := B) t ht n
local notation "q" => coefficientAmpleToOriginal (S := C) (algebraMap A B t)
  (coefficientParameter_isUnit (S := B) t ht) n
local notation "r" => ampleCurveTransport (e) n
local notation "f" => coefficientAmpleToOriginal (S := C) t ht n
local notation "H" => Sigma.snd (Subtype.val (ampleUniversalLevel (E) n))
local notation "U" => Sigma.fst (Subtype.val (ampleUniversalLevel (E) n))

/-- Successive coefficient recovery retains both actual compatible subgroup comparisons. -/
irreducible_def successiveCoefficientAmpleSubgroupIso :
    CompatibleIso (ampleUniversalLevel (D) n).val.2 ((H).baseChange ((q) ≫ (p))) :=
  compatiblePresentationExtension (H) (p) (coefficientAmpleSubgroupIso (S := B) t ht n)
    (q) (coefficientAmpleSubgroupIso (S := C) (algebraMap A B t)
      (coefficientParameter_isUnit (S := B) t ht) n)

omit [Algebra A C] [IsScalarTower A B C] in
/-- The successive comparison retains both original whole-cubic projections. -/
@[reassoc] theorem successiveCoefficientAmpleSubgroupIso_curve_fst :
    (successiveCoefficientAmpleSubgroupIso A B C t ht n).curve.hom.curve.left ≫
        pullback.fst (U).curve.hom ((q) ≫ (p)) ≫
          pullback.fst (faithfulUniversalCurve (E) n).curve.hom (ampleParameterOpen (E) n).ι ≫
          pullback.fst (E).curve.hom (cyclicFaithfulParameter (E).group n).hom =
      pullback.fst (faithfulUniversalCurve (D) n).curve.hom (ampleParameterOpen (D) n).ι ≫
        pullback.fst (D).curve.hom (cyclicFaithfulParameter (D).group n).hom ≫
        coefficientMorphism (S := C) (algebraMap A B t) ≫ coefficientMorphism (S := B) t := by
  rw [successiveCoefficientAmpleSubgroupIso_def]
  change ((coefficientAmpleSubgroupIso (S := C) (algebraMap A B t)
      (coefficientParameter_isUnit (S := B) t ht) n).curve.hom.curve.left ≫
    (baseChangeMap (q) (coefficientAmpleSubgroupIso (S := B) t ht n).curve.hom).curve.left ≫
      (compatibleBaseChangeComp (H) (p) (q)).curve.inv.curve.left) ≫ _ ≫ _ ≫ _ = _
  simp only [Category.assoc, compatibleBaseChangeComp_inv_curve_fst_assoc,
    baseChangeMap_fst_assoc]
  have hb := congrArg (fun z ↦
    (coefficientAmpleSubgroupIso (S := C) (algebraMap A B t)
      (coefficientParameter_isUnit (S := B) t ht) n).curve.hom.curve.left ≫
      pullback.fst (ampleUniversalLevel (F) n).val.1.curve.hom (q) ≫ z)
    (coefficientAmpleSubgroupIso_curve_fst (S := B) t ht n)
  refine hb.trans ?_
  have hc := congrArg (· ≫ coefficientMorphism (S := B) t)
    (coefficientAmpleSubgroupIso_curve_fst (S := C) (algebraMap A B t)
      (coefficientParameter_isUnit (S := B) t ht) n)
  simp only [Category.assoc] at hc
  exact hc

/-- Parameter transport retains the direct original cubic after both coefficient projections. -/
theorem coefficientAmpleParameterSubgroupIso_curve_fst :
    (ampleCurveTransportSubgroupIso (e) n).curve.hom.curve.left ≫
        pullback.fst (ampleUniversalLevel (D) n).val.1.curve.hom (r) ≫
          pullback.fst (faithfulUniversalCurve (D) n).curve.hom (ampleParameterOpen (D) n).ι ≫
            pullback.fst (D).curve.hom (cyclicFaithfulParameter (D).group n).hom ≫
              coefficientMorphism (S := C) (algebraMap A B t) ≫ coefficientMorphism (S := B) t =
      pullback.fst (faithfulUniversalCurve (G) n).curve.hom (ampleParameterOpen (G) n).ι ≫
        pullback.fst (G).curve.hom (cyclicFaithfulParameter (G).group n).hom ≫
          coefficientMorphism (S := C) t := by
  have hp := congrArg
    (· ≫ coefficientMorphism (S := C) (algebraMap A B t) ≫ coefficientMorphism (S := B) t)
    (ampleCurveTransportSubgroupIso_curve_fst (e) n)
  simp only [Category.assoc] at hp
  refine hp.trans ?_
  rw [parameterIso_curve]
  exact congrArg (pullback.fst (faithfulUniversalCurve (G) n).curve.hom
    (ampleParameterOpen (G) n).ι ≫
    pullback.fst (G).curve.hom (cyclicFaithfulParameter (G).group n).hom ≫ ·)
    (coefficientMorphism_tower A B C t)

local notation "L" => CompatibleIso.trans (ampleCurveTransportSubgroupIso (e) n)
  (CompatibleIso.baseChange (successiveCoefficientAmpleSubgroupIso A B C t ht n) (r))
local notation "R" => CompatibleIso.trans (coefficientAmpleSubgroupIso (S := C) t ht n)
  (compatibleBaseChangeCompEq (H) ((q) ≫ (p)) (r) (f)
    (Eq.symm (coefficientAmpleToOriginal_tower A B C t ht n)))

/-- Both full subgroup routes have the same actual original whole-curve projection. -/
theorem coefficientAmpleSubgroupIso_tower_curve_projection :
    (L).curve.hom.curve.left ≫ pullback.fst ((U).baseChange ((q) ≫ (p))).curve.hom (r) ≫
        pullback.fst (U).curve.hom ((q) ≫ (p)) ≫
          pullback.fst (faithfulUniversalCurve (E) n).curve.hom (ampleParameterOpen (E) n).ι ≫
            pullback.fst (E).curve.hom (cyclicFaithfulParameter (E).group n).hom =
      (R).curve.hom.curve.left ≫ pullback.fst ((U).baseChange ((q) ≫ (p))).curve.hom (r) ≫
        pullback.fst (U).curve.hom ((q) ≫ (p)) ≫
          pullback.fst (faithfulUniversalCurve (E) n).curve.hom (ampleParameterOpen (E) n).ι ≫
            pullback.fst (E).curve.hom (cyclicFaithfulParameter (E).group n).hom := by
  rw [CompatibleIso.trans_baseChange_curve_fst_assoc,
    CompatibleIso.trans_compEq_curve_fst_assoc,
    successiveCoefficientAmpleSubgroupIso_curve_fst]
  exact (coefficientAmpleParameterSubgroupIso_curve_fst A B C t ht n).trans
    (coefficientAmpleSubgroupIso_curve_fst (S := C) t ht n).symm


/-- The coefficient cocycle holds for full curves, subgroups and inclusions on the whole chart. -/
theorem coefficientAmpleSubgroupIso_tower :
    (ampleCurveTransportSubgroupIso (e) n).trans
      ((successiveCoefficientAmpleSubgroupIso A B C t ht n).baseChange (r)) =
    (coefficientAmpleSubgroupIso (S := C) t ht n).trans
      (compatibleBaseChangeCompEq (H) ((q) ≫ (p)) (r) (f)
        (coefficientAmpleToOriginal_tower A B C t ht n).symm) := by
  let pb := (IsPullback.of_hasPullback ((U).baseChange ((q) ≫ (p))).curve.hom (r)).paste_horiz
    ((IsPullback.of_hasPullback (U).curve.hom ((q) ≫ (p))).paste_horiz
      ((IsPullback.of_hasPullback (faithfulUniversalCurve (E) n).curve.hom
        (ampleParameterOpen (E) n).ι).paste_horiz
          (IsPullback.of_hasPullback (E).curve.hom
            (cyclicFaithfulParameter (E).group n).hom)))
  apply CompatibleIso.ext_curve_projection _ _ _ _ _ pb
  exact coefficientAmpleSubgroupIso_tower_curve_projection A B C t ht n

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
