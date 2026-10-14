/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointCubicBaseChange
public import FLT.Mazur.PolygonCompletePointIdentityOpenMarking
public import FLT.Mazur.CartesianOpenIsoBaseChange
public import FLT.Mazur.WeierstrassIntegralFaithfullyFlat

/-!
# Identity neighborhoods on every specified Cartesian family

The actual cubic comparison remains an isomorphism over the pulled-back
identity neighborhood. This includes the original closed polygon fiber,
and its original marking maps to the unchanged base-changed zero section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointIdentityCubicOpen

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
  {S Y : Scheme} (s : S ⟶ Spec (.of (PowerSeries K)))
  (p : Y ⟶ exactVeroneseProj K n h) (q : Y ⟶ S)
  (hs : IsPullback p q (exactVeroneseProjToBase K n h) s) (i : Fin n)
local notation "S₀" => Spec (CommRingCat.of (PowerSeries K))
local notation "W" => completePointWeierstrassCurve K n h i
local notation "c" => integralCurveStructure (W)
local notation "gS" => completePointToCubicBaseChange K n h s p q hs i
local notation "mS" => completeCartesianMarking K n h s p q hs i

/-- The actual pulled-back identity neighborhood on the original changed cubic. -/
def completePointIdentityBaseChangeOpen : (completePointCubicBaseChange K n h s i).Opens :=
  pullback.fst (c) (s ≫ (S₀).toSpecΓ) ⁻¹ᵁ completePointIdentityCubicOpen K n h i

/-- The original comparison is an isomorphism over the identity open on any specified square. -/
theorem completePointIdentityBaseChangeOpen_isIso :
    IsIso ((gS) ∣_ completePointIdentityBaseChangeOpen K n h s i) := by
  let _ := completePointIdentityCubicOpen_isIso K n h i
  exact CartesianOpenIsoBaseChange.isIso_restrict
    (completePointToCubicBaseChange_isPullback K n h s p q hs i) _

/-- The original changed zero section, with the same named target as the changed cubic map. -/
def completePointCubicChangedZero : S ⟶ completePointCubicBaseChange K n h s i :=
  integralCurveBaseChangeZero (W) (s ≫ (S₀).toSpecΓ)

/-- The changed zero section projects to the original cubic zero section. -/
@[reassoc] theorem completePointCubicChangedZero_fst :
    completePointCubicChangedZero K n h s i ≫ pullback.fst (c) (s ≫ (S₀).toSpecΓ) =
      (s ≫ (S₀).toSpecΓ) ≫ integralCurveZero (W) :=
  pullback.lift_fst _ _ _

/-- The original marking is sent to the actual base-changed cubic zero section. -/
@[reassoc] theorem completePointToCubicBaseChange_marking :
    (mS) ≫ (gS) = completePointCubicChangedZero K n h s i := by
  apply pullback.hom_ext
  · rw [Category.assoc, completePointToCubicBaseChange_fst,
      completeCartesianMarking_fst_assoc, completePointToIntegralCubic_marking]
    exact (Category.assoc _ _ _).symm.trans (pullback.lift_fst _ _ _).symm
  · rw [Category.assoc, completePointToCubicBaseChange_snd,
      completeCartesianMarking_snd, completePointCubicChangedZero,
      integralCurveBaseChangeZero_structure]

/-- Every value of the changed zero section lies in the changed identity open. -/
theorem completePointIdentityBaseChangeOpen_zero_range :
    Set.range (completePointCubicChangedZero K n h s i) ⊆
      completePointIdentityBaseChangeOpen K n h s i := by
  rintro _ ⟨x, rfl⟩
  change (completePointCubicChangedZero K n h s i ≫
    pullback.fst (c) (s ≫ (S₀).toSpecΓ)) x ∈ completePointIdentityCubicOpen K n h i
  rw [completePointCubicChangedZero_fst]
  exact completePointIdentityCubicOpen_zero_range K n h i ⟨_, rfl⟩

/-- The whole original marking is retained in the source of the changed local isomorphism. -/
theorem completePointIdentityBaseChangeOpen_marking_range :
    Set.range (mS) ⊆ (gS) ⁻¹ᵁ completePointIdentityBaseChangeOpen K n h s i := by
  rintro _ ⟨x, rfl⟩
  change ((mS) ≫ (gS)) x ∈ completePointIdentityBaseChangeOpen K n h s i
  rw [completePointToCubicBaseChange_marking]
  exact completePointIdentityBaseChangeOpen_zero_range K n h s i ⟨x, rfl⟩

end FLT.Mazur.PolygonInfinitesimalStages
