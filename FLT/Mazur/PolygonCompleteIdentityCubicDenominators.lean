/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityAdicCubicCoordinates
public import FLT.Mazur.ModuleSectionRatioOpenNaturality
public import FLT.Mazur.LineBundleSectionOpenPullback

/-!
# Change of actual cubic denominators before adic specialization

On a common complete patch the original cubic coordinates are ratios of
the same pulled-back pole sections. Transition denominators are units and
the cross-multiplied coordinate identities hold in the complete ring.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.PolygonInfinitesimalStages
open FCurve ModuleLineBundleTensorPullback WeierstrassIntegralChart
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic originalStageToCompatibleProj
  completeIdentityActionAdicChartSpaceMap completeIdentityActionAdicLiftSpaceMap
  ModuleSheafTensor.tensor
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (m : ℕ) (i j : Fin n)
variable (U : (completeIdentityActionAdicChartAmbientOpen K n h m i j).toScheme.affineOpens)
local notation "W" => completeIdentityAdicAmbientTargetPatch K n h m i j U
local notation "Y" => completeIdentityActionLiftSpace K n h
local notation "E" => completePointWeierstrassCurve K n h (0 : Fin n)
local notation "M" => tensorPower (completePointLine K n h (0 : Fin n)) 3
local notation "T" => completePointProjectiveSections K n h (0 : Fin n)
local notation "O" k => sectionGeneratorOpen (M) (T k)
local notation "C" k => completeIdentityCubicChartOpen K n h k
local notation "q" => pullback.snd (completeIdentityActionTarget K n h 0)
  (completePointToIntegralCubic K n h 0)
local notation "N" => Functor.obj (Scheme.Modules.pullback (q)) (M)
local notation "t" k => pullGlobal (q) (M) (T k)
local notation "F" => completeIdentityCubicPatchFunctions K n h m i j U

/-- The original denominator section generates on the whole complete coordinate patch. -/
theorem completeIdentityCubicPatch_generator (k : Fin 3) (hk : (W).1 ≤ C k) :
    (W).1 ≤ sectionGeneratorOpen (N) (t k) := by
  rw [sectionGeneratorOpen_pullGlobal
    ((completePointLine_locallyFreeRankOne K n h 0).tensorPower 3)]
  exact hk

/-- Restricting the action coordinates retains the original contraction's section pullback. -/
theorem completeIdentityCubicPatchFunctions_pullback (k l : Fin 3) (hk : (W).1 ≤ C k) :
    (F k hk) (coord (E) k l) =
      (q).appLE (O k) (W).1 hk (sectionRatioOn (M) (T k) (O k) le_rfl (T l)) := by
  unfold completeIdentityCubicPatchFunctions
  simp only [RingHom.comp_apply]
  rw [completeIdentityCubicFunctions_coordinate, ← Scheme.Hom.resLE_eq_morphismRestrict]
  simp only [Scheme.Hom.appTop, Scheme.Hom.resLE_app_top, CommRingCat.comp_apply,
    Iso.inv_hom_id_apply]
  change ((q).appLE (O k) (C k) le_rfl ≫
    (Y).presheaf.map (homOfLE hk).op) _ = _
  rw [Scheme.Hom.appLE_map]

/-- The actual complete coordinates are ratios in one original pulled-back line. -/
theorem completeIdentityCubicPatchFunctions_ratio (k l : Fin 3) (hk : (W).1 ≤ C k) :
    (F k hk) (coord (E) k l) = sectionRatioOn (N) (t k) (W).1
      (completeIdentityCubicPatch_generator K n h m i j U k hk) (t l) := by
  rw [completeIdentityCubicPatchFunctions_pullback]
  exact sectionRatioOn_pullback (q) (M) (O k) (W).1 hk (T k) (T l) le_rfl _

/-- All cubic chart changes obey the exact cross-multiplied identity in the complete ring. -/
theorem completeIdentityCubicPatchFunctions_transition (k l r : Fin 3)
    (hk : (W).1 ≤ C k) (hl : (W).1 ≤ C l) :
    (F k hk) (coord (E) k l) * (F l hl) (coord (E) l r) =
      (F k hk) (coord (E) k r) := by
  simp only [completeIdentityCubicPatchFunctions_ratio]
  exact sectionRatioOn_change (N) (t k) (t l) (t r) (W).1 _ _

/-- The actual transition denominator is a unit before taking the original adic quotient. -/
theorem completeIdentityCubicPatchFunctions_transition_unit (k l : Fin 3)
    (hk : (W).1 ≤ C k) (hl : (W).1 ≤ C l) :
    IsUnit ((F k hk) (coord (E) k l)) := by
  rw [completeIdentityCubicPatchFunctions_ratio]
  exact sectionRatioOn_isUnit (N) (t k) (t l) (W).1 _
    (completeIdentityCubicPatch_generator K n h m i j U l hl)

end FLT.Mazur.PolygonInfinitesimalStages
