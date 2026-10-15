/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.PolygonCompleteClosedFiber
public import FLT.Mazur.PolygonCoconeComparison

/-!
# Entire specified pinching models in the original complete closed fiber

The comparison uses the proved pushout of the original endpoint diagram.
It retains the complete normalization and every node, including their maps
into the complete total space. It is a comparison over the residue field.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completeClosedFiberInclusion
variable (K : Type) [Field K] (n : ℕ) (hn : 2 ≤ n) [NeZero n]
  {C : Over (Spec (.of K))} (p : components K n ⟶ C) (q : nodes K n ⟶ C)
  (hp : IsPushout (toComponents K n (by omega)) (toNodes K n) p q)
local notation "π" => exactVeroneseProjToBase K n hn
local notation "e" => IsPushout.isoIsPushout _ _
  (PolygonCyclicPushout.isPushout K n hn (by omega)) hp

/-- The entire original pinching model is the actual complete closed fiber. -/
def pinchingCompleteClosedIso : C.left ≅ pullback π (completeClosedBase K) :=
  (Over.forget _).mapIso (e).symm ≪≫ completeClosedFiberIso K n hn

/-- The comparison keeps the original coefficient projection. -/
@[reassoc] theorem pinchingCompleteClosedIso_snd :
    (pinchingCompleteClosedIso K n hn p q hp).hom ≫ pullback.snd _ _ = C.hom := by
  rw [pinchingCompleteClosedIso, Iso.trans_hom, Category.assoc, completeClosedFiberIso_snd]
  exact (e).inv.w

/-- The full normalization, including both endpoints of each component, is retained. -/
@[reassoc] theorem pinchingCompleteClosedIso_normalization :
    p.left ≫ (pinchingCompleteClosedIso K n hn p q hp).hom =
      (PolygonCyclicAtlas.normalization K n hn).left ≫
        (completeClosedFiberIso K n hn).hom := by
  rw [pinchingCompleteClosedIso, Iso.trans_hom, ← Category.assoc]
  congr 1
  exact congrArg Over.Hom.left
    ((PolygonCyclicPushout.isPushout K n hn (by omega)).inl_isoIsPushout_inv _ _ hp)

/-- The entire original node coproduct is retained. -/
@[reassoc] theorem pinchingCompleteClosedIso_nodes :
    q.left ≫ (pinchingCompleteClosedIso K n hn p q hp).hom =
      (PolygonCyclicAtlas.nodes K n hn).left ≫ (completeClosedFiberIso K n hn).hom := by
  rw [pinchingCompleteClosedIso, Iso.trans_hom, ← Category.assoc]
  congr 1
  exact congrArg Over.Hom.left
    ((PolygonCyclicPushout.isPushout K n hn (by omega)).inr_isoIsPushout_inv _ _ hp)

/-- Each complete original component has its original inclusion into the complete family. -/
@[reassoc] theorem pinchingCompleteClosedIso_component (i : Fin n) :
    (componentι K n i ≫ p).left ≫ (pinchingCompleteClosedIso K n hn p q hp).hom ≫
        pullback.fst _ _ =
      (componentι K n i ≫ PolygonCyclicAtlas.normalization K n hn).left ≫
        completeClosedFiberInclusion K n hn := by
  change (componentι K n i).left ≫ p.left ≫ _ ≫ _ = _
  rw [pinchingCompleteClosedIso_normalization_assoc, completeClosedFiberIso_fst]
  rfl

/-- Each singular section has its original inclusion into the complete family. -/
@[reassoc] theorem pinchingCompleteClosedIso_node (i : Fin n) :
    (nodeι K n i ≫ q).left ≫ (pinchingCompleteClosedIso K n hn p q hp).hom ≫
        pullback.fst _ _ =
      (nodeι K n i ≫ PolygonCyclicAtlas.nodes K n hn).left ≫
        completeClosedFiberInclusion K n hn := by
  change (nodeι K n i).left ≫ q.left ≫ _ ≫ _ = _
  rw [pinchingCompleteClosedIso_nodes_assoc, completeClosedFiberIso_fst]
  rfl

end FLT.Mazur.PolygonInfinitesimalStages
