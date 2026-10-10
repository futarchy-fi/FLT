/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassModificationXFullNodePushout
public import FLT.Mazur.WeierstrassModificationXFullNodeGeometry

/-!
# Pinching on the two original tangent opens of the full fiber

Both original fiber localizations inherit scheme pushouts through their
specified oriented node comparisons. Their actual inclusions are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
universe u
variable {K : Type u} [Field K] (a c : K) (ha : IsUnit a)
local notation "s₀" => fullNodeNormalizedDenominator a c
local notation "h₀" => fullNodeNormalizedDenominator_value a c ha
local notation "s₁" => fullNodeNormalizedDenominator (-a) c
local notation "h₁" => fullNodeNormalizedDenominator_value (-a) c ha.neg

/-- Both branches pinch to the exact original open where the opposite tangent is invertible. -/
theorem fullFirstFiberBranches_isPushout :
    IsPushout (NodeLocalDescent.firstOrigin K s₀ h₀) (NodeLocalDescent.secondOrigin K s₀ h₀)
      (fullNodeFirstBranch a c ha ≫ (fullFirstNodeIso a c ha).hom)
      (fullNodeSecondBranch a c ha ≫ (fullFirstNodeIso a c ha).hom) :=
  (fullNodeBranches_isPushout a c ha).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (fullFirstNodeIso a c ha)
    (by simp) (by simp) (by simp) (by simp)

/-- The other original tangent open keeps the opposite sign in its actual branch sources. -/
theorem fullSecondFiberBranches_isPushout :
    IsPushout (NodeLocalDescent.firstOrigin K s₁ h₁) (NodeLocalDescent.secondOrigin K s₁ h₁)
      (fullNodeFirstBranch (-a) c ha.neg ≫ (fullSecondNodeIso a c ha).hom)
      (fullNodeSecondBranch (-a) c ha.neg ≫ (fullSecondNodeIso a c ha).hom) :=
  (fullNodeBranches_isPushout (-a) c ha.neg).of_iso
    (Iso.refl _) (Iso.refl _) (Iso.refl _) (fullSecondNodeIso a c ha)
    (by simp) (by simp) (by simp) (by simp)

/-- Compatible branch maps descend uniquely on the original first fiber localization. -/
theorem fullFirstFiber_exists_unique_desc {Y : Scheme.{u}}
    (f : Spec (.of (Localization.Away (PolygonNodeEqualizer.first s₀))) ⟶ Y)
    (g : Spec (.of (Localization.Away (PolygonNodeEqualizer.second s₀))) ⟶ Y)
    (w : NodeLocalDescent.firstOrigin K s₀ h₀ ≫ f =
      NodeLocalDescent.secondOrigin K s₀ h₀ ≫ g) :
    ∃! d : Spec (.of (FullFirstFiberOpen a c)) ⟶ Y,
      (fullNodeFirstBranch a c ha ≫ (fullFirstNodeIso a c ha).hom) ≫ d = f ∧
      (fullNodeSecondBranch a c ha ≫ (fullFirstNodeIso a c ha).hom) ≫ d = g := by
  let H := fullFirstFiberBranches_isPushout a c ha
  refine ⟨H.desc f g w, ⟨H.inl_desc f g w, H.inr_desc f g w⟩, ?_⟩
  intro d hd
  exact H.hom_ext (hd.1.trans (H.inl_desc f g w).symm)
    (hd.2.trans (H.inr_desc f g w).symm)

/-- Compatible maps also descend on the original second fiber localization. -/
theorem fullSecondFiber_exists_unique_desc {Y : Scheme.{u}}
    (f : Spec (.of (Localization.Away (PolygonNodeEqualizer.first s₁))) ⟶ Y)
    (g : Spec (.of (Localization.Away (PolygonNodeEqualizer.second s₁))) ⟶ Y)
    (w : NodeLocalDescent.firstOrigin K s₁ h₁ ≫ f =
      NodeLocalDescent.secondOrigin K s₁ h₁ ≫ g) :
    ∃! d : Spec (.of (FullSecondFiberOpen a c)) ⟶ Y,
      (fullNodeFirstBranch (-a) c ha.neg ≫ (fullSecondNodeIso a c ha).hom) ≫ d = f ∧
      (fullNodeSecondBranch (-a) c ha.neg ≫ (fullSecondNodeIso a c ha).hom) ≫ d = g := by
  let H := fullSecondFiberBranches_isPushout a c ha
  refine ⟨H.desc f g w, ⟨H.inl_desc f g w, H.inr_desc f g w⟩, ?_⟩
  intro d hd
  exact H.hom_ext (hd.1.trans (H.inl_desc f g w).symm)
    (hd.2.trans (H.inr_desc f g w).symm)

end FLT.Mazur.WeierstrassModificationX
