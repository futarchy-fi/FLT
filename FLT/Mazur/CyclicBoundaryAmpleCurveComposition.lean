/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryCurveTransportCoherence
public import FLT.Mazur.CyclicBoundaryAmpleCurveProjection
public import FLT.Mazur.CompatibleSubgroupBaseChangeCoherence

/-!
# Full subgroup composition for ample curve transport

The actual compatible subgroup comparisons compose with the canonical
iterated-pullback comparison. Equality is proved on the original whole-curve
projection, using the pasted cartesian square and faithfulness of subgroup inclusion.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] ampleCurveTransportSubgroupIso
variable {S : Scheme} {E F G : GeneralizedEllipticCurve S}
  [IsSeparated E.group.hom] [IsSeparated F.group.hom] [IsSeparated G.group.hom]
  [SmoothOfRelativeDimension 1 E.group.hom]
  [SmoothOfRelativeDimension 1 F.group.hom] [SmoothOfRelativeDimension 1 G.group.hom]
  (e : E ≅ F) (d : F ≅ G) (n : ℕ) [NeZero n]
local notation "q₁" => ampleCurveTransport e n
local notation "q₂" => ampleCurveTransport d n
local notation "q₃" => ampleCurveTransport (e ≪≫ d) n
local notation "w" => Eq.symm (ampleCurveTransport_comp e d n)
local notation "H" => Sigma.snd (Subtype.val (ampleUniversalLevel G n))
local notation "A" => Sigma.fst (Subtype.val (ampleUniversalLevel G n))

/-- Full curve and subgroup transport obey the same actual composition law as the parameters. -/
theorem ampleCurveTransportSubgroupIso_comp :
    (ampleCurveTransportSubgroupIso e n).trans
      ((ampleCurveTransportSubgroupIso d n).baseChange (q₁)) =
    (ampleCurveTransportSubgroupIso (e ≪≫ d) n).trans
      (compatibleBaseChangeCompEq (H) (q₂) (q₁) (q₃) (w)) := by
  apply CompatibleIso.ext_curve_hom
  change (ampleCurveTransportSubgroupIso e n).curve.hom ≫
      (baseChangeFunctor (q₁)).map (ampleCurveTransportSubgroupIso d n).curve.hom =
    (ampleCurveTransportSubgroupIso (e ≪≫ d) n).curve.hom ≫
      (compatibleBaseChangeCompEq (H) (q₂) (q₁) (q₃) (w)).curve.hom
  rw [compatibleBaseChangeCompEq_curve]
  apply forgetCurve.map_injective
  apply Over.OverMorphism.ext
  let pb := (IsPullback.of_hasPullback ((A).baseChange (q₂)).curve.hom (q₁)).paste_horiz
    ((IsPullback.of_hasPullback (A).curve.hom (q₂)).paste_horiz
      ((IsPullback.of_hasPullback (faithfulUniversalCurve G n).curve.hom
        (ampleParameterOpen G n).ι).paste_horiz
          (IsPullback.of_hasPullback G.curve.hom (cyclicFaithfulParameter G.group n).hom)))
  apply pb.hom_ext
  · change ((ampleCurveTransportSubgroupIso e n).curve.hom.curve.left ≫
        (baseChangeMap (q₁) (ampleCurveTransportSubgroupIso d n).curve.hom).curve.left) ≫
          pullback.fst ((A).baseChange (q₂)).curve.hom (q₁) ≫
            pullback.fst (A).curve.hom (q₂) ≫
              pullback.fst (faithfulUniversalCurve G n).curve.hom (ampleParameterOpen G n).ι ≫
                pullback.fst G.curve.hom (cyclicFaithfulParameter G.group n).hom =
      ((ampleCurveTransportSubgroupIso (e ≪≫ d) n).curve.hom.curve.left ≫
        ((A).baseChangeCompEqIso (q₂) (q₁) (q₃) (w)).hom.curve.left) ≫
          pullback.fst ((A).baseChange (q₂)).curve.hom (q₁) ≫
            pullback.fst (A).curve.hom (q₂) ≫
              pullback.fst (faithfulUniversalCurve G n).curve.hom (ampleParameterOpen G n).ι ≫
                pullback.fst G.curve.hom (cyclicFaithfulParameter G.group n).hom
    simp only [Category.assoc, baseChangeMap_fst_assoc,
      baseChangeCompEqIso_curve_fst_assoc]
    dsimp only [ampleUniversalLevel]
    rw [ampleCurveTransportSubgroupIso_curve_fst,
      ampleCurveTransportSubgroupIso_curve_fst_assoc, ampleCurveTransportSubgroupIso_curve_fst]
    rfl
  · exact (Over.w _).trans (Over.w _).symm

end FLT.Mazur.CyclicBoundaryParameter
