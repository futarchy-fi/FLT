/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicBoundaryCurveTransport
public import FLT.Mazur.CyclicBoundaryBaseChangeSubgroup

/-!
# Full universal subgroups under boundary curve transport

The parameter isomorphism induced by a full curve comparison carries the
actual universal curve and every cyclic section to the original pullback.
Consequently the finite subgroup, its inclusion and its generator are retained.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.CyclicBoundaryParameter
open GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {E F : GeneralizedEllipticCurve S}
  [IsSeparated E.group.hom] [IsSeparated F.group.hom]
  (e : E ≅ F) (n : ℕ) [NeZero n]
local notation "P" => cyclicFaithfulParameter E.group n
local notation "Q" => cyclicFaithfulParameter F.group n
local notation "q" => Over.Hom.left (Iso.hom (faithfulCurveTransportIso e n))

/-- The full curve comparison over the transported actual parameter scheme. -/
def faithfulTransportCurveIso :
    faithfulUniversalCurve E n ≅ (faithfulUniversalCurve F n).baseChange (q) :=
  (baseChangeFunctor (P).hom).mapIso e ≪≫
    F.baseChangeCompEqIso (Q).hom (q) (P).hom
      (faithfulCurveTransportIso e n).hom.w.symm

/-- The universal curve transport retains the given whole-curve morphism. -/
@[reassoc] theorem faithfulTransportCurveIso_curve_fst :
    (faithfulTransportCurveIso e n).hom.curve.left ≫
      pullback.fst (faithfulUniversalCurve F n).curve.hom (q) ≫
        pullback.fst F.curve.hom (Q).hom =
      pullback.fst E.curve.hom (P).hom ≫ e.hom.curve.left := by
  change ((baseChangeMap (P).hom e.hom).curve.left ≫
    (F.baseChangeCompEqIso (Q).hom (q) (P).hom _).hom.curve.left) ≫ _ = _
  rw [Category.assoc]
  exact (congrArg ((baseChangeMap (P).hom e.hom).curve.left ≫ ·)
    (F.baseChangeCompEqIso_curve_fst (Q).hom (q) (P).hom
      (faithfulCurveTransportIso e n).hom.w.symm)).trans (baseChangeMap_fst _ _)

/-- The smooth-group transport retains the given group morphism. -/
@[reassoc] theorem faithfulTransportCurveIso_group_fst :
    (faithfulTransportCurveIso e n).hom.group.left ≫
      pullback.fst (faithfulUniversalCurve F n).group.hom (q) ≫
        pullback.fst F.group.hom (Q).hom =
      pullback.fst E.group.hom (P).hom ≫ e.hom.group.left := by
  change (((Over.pullback (P).hom).map e.hom.group).left ≫
    (F.baseChangeCompEqIso (Q).hom (q) (P).hom _).hom.group.left) ≫ _ = _
  rw [Category.assoc]
  refine (congrArg (((Over.pullback (P).hom).map e.hom.group).left ≫ ·)
    (F.baseChangeCompEqIso_group_fst (Q).hom (q) (P).hom
      (faithfulCurveTransportIso e n).hom.w.symm)).trans ?_
  simp only [Over.pullback_map_left, pullback.lift_fst]

/-- Each universal cyclic section is carried to its original pulled-back section. -/
theorem faithfulTransportCurveIso_section (i : Multiplicative (ZMod n)) :
    faithfulUniversalMarking E n i ≫ (faithfulTransportCurveIso e n).hom.group =
      GroupSectionBaseChange.pullSection (q) (faithfulUniversalMarking F n i) := by
  apply OverPullbackSection.hom_ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, faithfulTransportCurveIso_group_fst,
      GroupSectionBaseChange.section_fst_assoc]
    rw [faithfulUniversalMarking_original_fst_assoc,
      faithfulUniversalMarking_original_fst]
    have he := congrArg Over.Hom.left (faithfulCurveTransport_value e n (𝟙 _) (1, 1, i))
    simpa only [faithfulCurveTransportIso, Over.comp_left, Over.id_left,
      Category.id_comp] using he.symm
  · have hp (s : 𝟙_ (Over (P).left) ⟶ ((faithfulUniversalCurve F n).baseChange (q)).group) :
        (s.left ≫ pullback.fst (faithfulUniversalCurve F n).group.hom (q)) ≫
          (faithfulUniversalCurve F n).group.hom = (q) := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      change (s.left ≫ ((faithfulUniversalCurve F n).baseChange (q)).group.hom) ≫ (q) = (q)
      rw [s.w]
      exact Category.id_comp _
    exact (hp _).trans (hp _).symm

/-- The original finite subgroup is preserved as a compatible full subgroup. -/
def faithfulTransportSubgroupIso :
    FiniteSubgroup.CompatibleIso (faithfulUniversalSubgroup E n)
      ((faithfulUniversalSubgroup F n).baseChange (q)) :=
  relativeCyclicSubgroupPullbackCompatibleIso (q)
    (faithfulUniversalMarking F n) (faithfulUniversalMarking E n)
    (faithfulUniversalMarking_distinct F n) (faithfulUniversalMarking_distinct E n)
    (faithfulTransportCurveIso e n) (faithfulTransportCurveIso_section e n)

/-- The compatible comparison retains the constructed full generalized-curve isomorphism. -/
theorem faithfulTransportSubgroupIso_curve :
    (faithfulTransportSubgroupIso e n).curve = faithfulTransportCurveIso e n := rfl

/-- The specified generator is retained by the actual subgroup comparison. -/
theorem faithfulTransportSubgroupIso_generator :
    (faithfulUniversalCurve E n).relativeCyclicGenerator (faithfulUniversalMarking E n)
        (faithfulUniversalMarking_distinct E n) ≫ (faithfulTransportSubgroupIso e n).subgroup.hom =
      GroupSectionBaseChange.pullSection (q)
        ((faithfulUniversalCurve F n).relativeCyclicGenerator (faithfulUniversalMarking F n)
          (faithfulUniversalMarking_distinct F n)) :=
  relativeCyclicSubgroupPullbackCompatibleIso_generator (q)
    (faithfulUniversalMarking F n) (faithfulUniversalMarking E n)
    (faithfulUniversalMarking_distinct F n) (faithfulUniversalMarking_distinct E n)
    (faithfulTransportCurveIso e n) (faithfulTransportCurveIso_section e n)

end FLT.Mazur.CyclicBoundaryParameter
