/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryAmpleCurveModuli
public import FLT.Mazur.CompatibleSubgroupPullbackCast

/-!
# Full curve projections of ample transport

The ample comparison retains the supplied whole-curve isomorphism on the
original curve projection. This identifies its actual geometry independently
of the casts used to restrict to the ample open.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S}
  [IsSeparated E.group.hom] [IsSeparated F.group.hom]
  [SmoothOfRelativeDimension 1 E.group.hom] [SmoothOfRelativeDimension 1 F.group.hom]
  (e : E ≅ F) (n : ℕ) [NeZero n]

attribute [local irreducible] faithfulCurveTransportIso faithfulTransportCurveIso
local notation "q" => Over.Hom.left (Iso.hom (faithfulCurveTransportIso e n))
local notation "I" => ampleParameterOpen E n
local notation "J" => ampleParameterOpen F n
local notation "A" => faithfulUniversalCurve E n
local notation "B" => faithfulUniversalCurve F n

/-- The ample comparison is the exact full compatible pullback transport. -/
theorem ampleCurveTransportSubgroupIso_eq :
    ampleCurveTransportSubgroupIso e n =
      (faithfulTransportTestSubgroupIso e n (I).ι).trans
        (compatibleBaseChangeCompEq (faithfulUniversalSubgroup F n) (J).ι
          (ampleCurveTransport e n) ((I).ι ≫ (q)) (ampleCurveTransport_inclusion e n).symm) :=
  compatibleBaseChangeCompEq_cast _ _ _ _ _ _

omit [SmoothOfRelativeDimension 1 E.group.hom] [SmoothOfRelativeDimension 1 F.group.hom] in
/-- Every test transport retains the given original whole-curve map. -/
@[reassoc] theorem faithfulTransportTestSubgroupIso_curve_fst {T : Scheme}
    (u : T ⟶ (cyclicFaithfulParameter E.group n).left) :
    (faithfulTransportTestSubgroupIso e n u).curve.hom.curve.left ≫
        pullback.fst (B).curve.hom (u ≫ (q)) ≫
          pullback.fst F.curve.hom (cyclicFaithfulParameter F.group n).hom =
      pullback.fst (A).curve.hom u ≫
        pullback.fst E.curve.hom (cyclicFaithfulParameter E.group n).hom ≫ e.hom.curve.left := by
  change ((baseChangeMap u (faithfulTransportCurveIso e n).hom).curve.left ≫
    (compatibleBaseChangeComp (faithfulUniversalSubgroup F n) (q) u).curve.inv.curve.left) ≫
      _ ≫ _ = _
  simp only [Category.assoc, compatibleBaseChangeComp_inv_curve_fst_assoc,
    baseChangeMap_fst_assoc, faithfulTransportCurveIso_curve_fst]

/-- Restricting to the ample open retains the original whole-curve morphism exactly. -/
@[reassoc] theorem ampleCurveTransportSubgroupIso_curve_fst :
    (ampleCurveTransportSubgroupIso e n).curve.hom.curve.left ≫
        pullback.fst ((B).baseChange (J).ι).curve.hom (ampleCurveTransport e n) ≫
          pullback.fst (B).curve.hom (J).ι ≫
            pullback.fst F.curve.hom (cyclicFaithfulParameter F.group n).hom =
      pullback.fst (A).curve.hom (I).ι ≫
        pullback.fst E.curve.hom (cyclicFaithfulParameter E.group n).hom ≫ e.hom.curve.left := by
  rw [ampleCurveTransportSubgroupIso_eq]
  change ((faithfulTransportTestSubgroupIso e n (I).ι).curve.hom.curve.left ≫
    (compatibleBaseChangeCompEq (faithfulUniversalSubgroup F n) (J).ι
      (ampleCurveTransport e n) ((I).ι ≫ (q)) _).curve.hom.curve.left) ≫ _ ≫ _ ≫ _ = _
  rw [Category.assoc, compatibleBaseChangeCompEq_curve_fst_assoc,
    faithfulTransportTestSubgroupIso_curve_fst]

end FLT.Mazur.CyclicBoundaryParameter
