/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArithmeticOneGonCoefficientFaithful
public import FLT.Mazur.CyclicBoundaryAmpleBaseChangeProjection
public import FLT.Mazur.CyclicBoundaryAmpleCurveProjection

/-!
# Whole-curve projections of arithmetic coefficient subgroup comparisons

Both the faithful and ample comparisons retain the original whole-cubic
coefficient morphism, not merely its effect on modular classes or points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.ArithmeticOneGonGeneralizedCurve
open CyclicBoundaryParameter GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
open OneGonSmoothing
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ampleCurveTransportSubgroupIso ampleBaseChangeSubgroupIso
  faithfulCurveTransportIso
variable {R S : Type} [CommRing R] [CommRing S] [Algebra R S]
  (t : R) (ht : IsUnit (1 + 432 * t)) (n : ℕ) [NeZero n]
local notation "g" => Spec.map (CommRingCat.ofHom (algebraMap R S))
local notation "E" => curve t ht
local notation "F" => curve (algebraMap R S t) (coefficientParameter_isUnit t ht)
local notation "U" => faithfulUniversalCurve (E) n
local notation "V" => faithfulUniversalCurve (F) n
local notation "q" => Over.Hom.left (Iso.hom (faithfulCurveTransportIso (coefficientIso t ht) n))
local notation "p" => faithfulBaseChangeToOriginal (g) (GeneralizedEllipticCurve.group (E)) n

local instance coefficientSubgroupProjection_separated :
    IsSeparated ((E).baseChange (g)).group.hom :=
  inferInstanceAs (IsSeparated (pullback.snd (E).group.hom (g)))

local instance coefficientSubgroupProjection_smooth :
    SmoothOfRelativeDimension 1 ((E).baseChange (g)).group.hom :=
  MorphismProperty.pullback_snd (P := @SmoothOfRelativeDimension 1) (E).group.hom (g)
    inferInstance

/-- The whole faithful subgroup comparison retains the original cubic coefficient morphism. -/
@[reassoc] theorem coefficientFaithfulSubgroupIso_curve_fst :
    (coefficientFaithfulSubgroupIso (S := S) t ht n).curve.hom.curve.left ≫
        pullback.fst (U).curve.hom (coefficientFaithfulToOriginal t ht n) ≫
          pullback.fst (E).curve.hom (cyclicFaithfulParameter (E).group n).hom =
      pullback.fst (F).curve.hom (cyclicFaithfulParameter (F).group n).hom ≫
        coefficientMorphism (S := S) t := by
  dsimp only [coefficientFaithfulToOriginal]
  change ((faithfulTransportSubgroupIso (coefficientIso t ht) n).curve.hom.curve.left ≫
    (baseChangeMap (q) (faithfulBaseChangeSubgroupIso (g) (E) n).curve.hom).curve.left ≫
      (compatibleBaseChangeComp (faithfulUniversalSubgroup (E) n) (p) (q)).curve.inv.curve.left)
        ≫ _ ≫ _ = _
  rw [faithfulTransportSubgroupIso_curve, faithfulBaseChangeSubgroupIso_curve]
  simp only [Category.assoc, compatibleBaseChangeComp_inv_curve_fst_assoc,
    baseChangeMap_fst_assoc, faithfulBaseChangeCurveIso_curve_fst]
  rw [faithfulTransportCurveIso_curve_fst_assoc]
  exact congrArg (pullback.fst (F).curve.hom
    (cyclicFaithfulParameter (F).group n).hom ≫ ·) (coefficientIso_curve_fst t ht)

/-- The ample comparison retains the two independent universal-curve comparisons. -/
@[reassoc] theorem coefficientAmpleSubgroupIso_curve_projection :
    (coefficientAmpleSubgroupIso (S := S) t ht n).curve.hom.curve.left ≫
        pullback.fst ((U).baseChange (ampleParameterOpen (E) n).ι).curve.hom
          (coefficientAmpleToOriginal t ht n) =
      (ampleCurveTransportSubgroupIso (coefficientIso t ht) n).curve.hom.curve.left ≫
        pullback.fst (ampleUniversalLevel ((E).baseChange (g)) n).val.1.curve.hom
          (ampleCurveTransport (coefficientIso t ht) n) ≫
        (ampleBaseChangeSubgroupIso (g) (E) n).curve.hom.curve.left ≫
          pullback.fst ((U).baseChange (ampleParameterOpen (E) n).ι).curve.hom
            (ampleBaseChangeToOriginal (g) (E) n) := by
  dsimp only [coefficientAmpleToOriginal]
  change ((ampleCurveTransportSubgroupIso (coefficientIso t ht) n).curve.hom.curve.left ≫
    (baseChangeMap (ampleCurveTransport (coefficientIso t ht) n)
      (ampleBaseChangeSubgroupIso (g) (E) n).curve.hom).curve.left ≫
      (compatibleBaseChangeComp (ampleUniversalLevel (E) n).val.2
        (ampleBaseChangeToOriginal (g) (E) n)
        (ampleCurveTransport (coefficientIso t ht) n)).curve.inv.curve.left) ≫ _ = _
  have hc := compatibleBaseChangeComp_inv_curve_fst (ampleUniversalLevel (E) n).val.2
    (ampleBaseChangeToOriginal (g) (E) n) (ampleCurveTransport (coefficientIso t ht) n)
  have hh := congrArg (fun z ↦
    (ampleCurveTransportSubgroupIso (coefficientIso t ht) n).curve.hom.curve.left ≫
      (baseChangeMap (ampleCurveTransport (coefficientIso t ht) n)
        (ampleBaseChangeSubgroupIso (g) (E) n).curve.hom).curve.left ≫ z) hc
  simp only [Category.assoc] at hh ⊢
  refine hh.trans ?_
  rw [baseChangeMap_fst_assoc]
  rfl

/-- The actual ample subgroup comparison retains the same whole-cubic coefficient morphism. -/
@[reassoc] theorem coefficientAmpleSubgroupIso_curve_fst :
    (coefficientAmpleSubgroupIso (S := S) t ht n).curve.hom.curve.left ≫
        pullback.fst ((U).baseChange (ampleParameterOpen (E) n).ι).curve.hom
          (coefficientAmpleToOriginal t ht n) ≫
        pullback.fst (U).curve.hom (ampleParameterOpen (E) n).ι ≫
          pullback.fst (E).curve.hom (cyclicFaithfulParameter (E).group n).hom =
      pullback.fst (V).curve.hom (ampleParameterOpen (F) n).ι ≫
        pullback.fst (F).curve.hom (cyclicFaithfulParameter (F).group n).hom ≫
          coefficientMorphism (S := S) t := by
  rw [coefficientAmpleSubgroupIso_curve_projection_assoc]
  have hc := ampleBaseChangeSubgroupIso_curve_fst (g) (E) n
  have hb := congrArg (fun z ↦
    (ampleCurveTransportSubgroupIso (coefficientIso t ht) n).curve.hom.curve.left ≫
      pullback.fst (ampleUniversalLevel ((E).baseChange (g)) n).val.1.curve.hom
        (ampleCurveTransport (coefficientIso t ht) n) ≫ z) hc
  refine hb.trans ?_
  have hd := congrArg (· ≫ pullback.fst (E).curve.hom (g))
    (ampleCurveTransportSubgroupIso_curve_fst (coefficientIso t ht) n)
  simp only [Category.assoc] at hd
  refine hd.trans ?_
  exact congrArg (pullback.fst (V).curve.hom (ampleParameterOpen (F) n).ι ≫
    pullback.fst (F).curve.hom (cyclicFaithfulParameter (F).group n).hom ≫ ·)
    (coefficientIso_curve_fst t ht)

end FLT.Mazur.ArithmeticOneGonGeneralizedCurve
