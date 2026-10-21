/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryCurveTransportCoherence
public import FLT.Mazur.CompatibleSubgroupBaseChangeCoherence

/-!
# Full subgroup composition for faithful curve transport

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
attribute [local irreducible] faithfulCurveTransportIso faithfulTransportCurveIso
variable {S : Scheme} {E F G : GeneralizedEllipticCurve S}
  [IsSeparated E.group.hom] [IsSeparated F.group.hom] [IsSeparated G.group.hom]
  (e : E ≅ F) (d : F ≅ G) (n : ℕ) [NeZero n]
local notation "q₁" => Over.Hom.left (Iso.hom (faithfulCurveTransportIso e n))
local notation "q₂" => Over.Hom.left (Iso.hom (faithfulCurveTransportIso d n))
local notation "q₃" => Over.Hom.left (Iso.hom (faithfulCurveTransportIso (e ≪≫ d) n))
local notation "w" => Eq.symm (congrArg Over.Hom.left (faithfulCurveTransportIso_comp e d n))
local notation "H" => faithfulUniversalSubgroup G n
local notation "A" => faithfulUniversalCurve G n

/-- Full curve and subgroup transport obey the same actual composition law as the parameters. -/
theorem faithfulTransportSubgroupIso_comp :
    (faithfulTransportSubgroupIso e n).trans
      ((faithfulTransportSubgroupIso d n).baseChange (q₁)) =
    (faithfulTransportSubgroupIso (e ≪≫ d) n).trans
      (compatibleBaseChangeCompEq (H) (q₂) (q₁) (q₃) (w)) := by
  apply CompatibleIso.ext_curve_hom
  change (faithfulTransportCurveIso e n).hom ≫
      (baseChangeFunctor (q₁)).map (faithfulTransportCurveIso d n).hom =
    (faithfulTransportCurveIso (e ≪≫ d) n).hom ≫
      (compatibleBaseChangeCompEq (H) (q₂) (q₁) (q₃) (w)).curve.hom
  rw [compatibleBaseChangeCompEq_curve]
  apply forgetCurve.map_injective
  apply Over.OverMorphism.ext
  let pb := (IsPullback.of_hasPullback ((A).baseChange (q₂)).curve.hom (q₁)).paste_horiz
    ((IsPullback.of_hasPullback (A).curve.hom (q₂)).paste_horiz
      (IsPullback.of_hasPullback G.curve.hom (cyclicFaithfulParameter G.group n).hom))
  apply pb.hom_ext
  · change ((faithfulTransportCurveIso e n).hom.curve.left ≫
        (baseChangeMap (q₁) (faithfulTransportCurveIso d n).hom).curve.left) ≫
          pullback.fst ((A).baseChange (q₂)).curve.hom (q₁) ≫
            pullback.fst (A).curve.hom (q₂) ≫
              pullback.fst G.curve.hom (cyclicFaithfulParameter G.group n).hom =
      ((faithfulTransportCurveIso (e ≪≫ d) n).hom.curve.left ≫
        ((A).baseChangeCompEqIso (q₂) (q₁) (q₃) (w)).hom.curve.left) ≫
          pullback.fst ((A).baseChange (q₂)).curve.hom (q₁) ≫
            pullback.fst (A).curve.hom (q₂) ≫
              pullback.fst G.curve.hom (cyclicFaithfulParameter G.group n).hom
    simp only [Category.assoc, baseChangeMap_fst_assoc,
      baseChangeCompEqIso_curve_fst_assoc, faithfulTransportCurveIso_curve_fst,
      faithfulTransportCurveIso_curve_fst_assoc]
    rfl
  · exact (Over.w _).trans (Over.w _).symm

end FLT.Mazur.CyclicBoundaryParameter
