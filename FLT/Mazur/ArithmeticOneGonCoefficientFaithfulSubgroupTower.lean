/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCoefficientFaithfulTower
public import FLT.Mazur.ArithmeticOneGonCoefficientSubgroupProjection
public import FLT.Mazur.CompatibleSubgroupPresentationExtension

/-!
# The coefficient cocycle for full faithful universal subgroups

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
local notation "p" => coefficientFaithfulToOriginal (S := B) t ht n
local notation "q" => coefficientFaithfulToOriginal (S := C) (algebraMap A B t)
  (coefficientParameter_isUnit (S := B) t ht) n
local notation "r" => Over.Hom.left (Iso.hom (faithfulCurveTransportIso (e) n))
local notation "f" => coefficientFaithfulToOriginal (S := C) t ht n
local notation "H" => faithfulUniversalSubgroup (E) n
local notation "U" => faithfulUniversalCurve (E) n

/-- Successive coefficient recovery retains both actual compatible subgroup comparisons. -/
def successiveCoefficientFaithfulSubgroupIso :
    CompatibleIso (faithfulUniversalSubgroup (D) n) ((H).baseChange ((q) ≫ (p))) :=
  compatiblePresentationExtension (H) (p) (coefficientFaithfulSubgroupIso (S := B) t ht n)
    (q) (coefficientFaithfulSubgroupIso (S := C) (algebraMap A B t)
      (coefficientParameter_isUnit (S := B) t ht) n)

omit [Algebra A C] [IsScalarTower A B C] in
/-- The successive comparison retains both original whole-cubic projections. -/
@[reassoc] theorem successiveCoefficientFaithfulSubgroupIso_curve_fst :
    (successiveCoefficientFaithfulSubgroupIso A B C t ht n).curve.hom.curve.left ≫
        pullback.fst (U).curve.hom ((q) ≫ (p)) ≫
          pullback.fst (E).curve.hom (cyclicFaithfulParameter (E).group n).hom =
      pullback.fst (D).curve.hom (cyclicFaithfulParameter (D).group n).hom ≫
        coefficientMorphism (S := C) (algebraMap A B t) ≫ coefficientMorphism (S := B) t := by
  change ((coefficientFaithfulSubgroupIso (S := C) (algebraMap A B t)
      (coefficientParameter_isUnit (S := B) t ht) n).curve.hom.curve.left ≫
    (baseChangeMap (q) (coefficientFaithfulSubgroupIso (S := B) t ht n).curve.hom).curve.left ≫
      (compatibleBaseChangeComp (H) (p) (q)).curve.inv.curve.left) ≫ _ ≫ _ = _
  simp only [Category.assoc, compatibleBaseChangeComp_inv_curve_fst_assoc,
    baseChangeMap_fst_assoc, coefficientFaithfulSubgroupIso_curve_fst,
    coefficientFaithfulSubgroupIso_curve_fst_assoc]

/-- The coefficient cocycle holds for full curves, subgroups and inclusions on the whole chart. -/
theorem coefficientFaithfulSubgroupIso_tower :
    (faithfulTransportSubgroupIso (e) n).trans
      ((successiveCoefficientFaithfulSubgroupIso A B C t ht n).baseChange (r)) =
    (coefficientFaithfulSubgroupIso (S := C) t ht n).trans
      (compatibleBaseChangeCompEq (H) ((q) ≫ (p)) (r) (f)
        (coefficientFaithfulToOriginal_tower n A B C t ht).symm) := by
  apply CompatibleIso.ext_curve_hom
  apply forgetCurve.map_injective
  apply Over.OverMorphism.ext
  let pb := (IsPullback.of_hasPullback ((U).baseChange ((q) ≫ (p))).curve.hom (r)).paste_horiz
    ((IsPullback.of_hasPullback (U).curve.hom ((q) ≫ (p))).paste_horiz
      (IsPullback.of_hasPullback (E).curve.hom (cyclicFaithfulParameter (E).group n).hom))
  apply pb.hom_ext
  · change ((faithfulTransportCurveIso (e) n).hom.curve.left ≫
        (baseChangeMap (r)
          (successiveCoefficientFaithfulSubgroupIso A B C t ht n).curve.hom).curve.left) ≫
        pullback.fst ((U).baseChange ((q) ≫ (p))).curve.hom (r) ≫
          pullback.fst (U).curve.hom ((q) ≫ (p)) ≫
            pullback.fst (E).curve.hom (cyclicFaithfulParameter (E).group n).hom =
      ((coefficientFaithfulSubgroupIso (S := C) t ht n).curve.hom.curve.left ≫
        (compatibleBaseChangeCompEq (H) ((q) ≫ (p)) (r) (f) _).curve.hom.curve.left) ≫
        pullback.fst ((U).baseChange ((q) ≫ (p))).curve.hom (r) ≫
          pullback.fst (U).curve.hom ((q) ≫ (p)) ≫
            pullback.fst (E).curve.hom (cyclicFaithfulParameter (E).group n).hom
    simp only [Category.assoc, baseChangeMap_fst_assoc,
      compatibleBaseChangeCompEq_curve_fst_assoc,
      successiveCoefficientFaithfulSubgroupIso_curve_fst,
      coefficientFaithfulSubgroupIso_curve_fst]
    rw [faithfulTransportCurveIso_curve_fst_assoc, parameterIso_curve,
      coefficientMorphism_tower]
  · exact (Over.w _).trans (Over.w _).symm

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
