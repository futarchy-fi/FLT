/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompletePointFirstOrderIdeal
public import FLT.Mazur.PolygonCompletePointFirstOrderLine
public import FLT.Mazur.GlobalIdealPowerCompatibility

/-!
# The original cubic origin pulls back to the full original marking

Glue the actual first-order Cartier comparisons with the original marking
complement. The resulting equality retains multiplicity on the entire family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
open WeierstrassIntegralChart FCurve FCurve.ModuleLineBundleTensorPullback
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase

variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "s" => completeBaseMarking K n h i
local notation "W" => completePointWeierstrassCurve K n h i
local notation "g" => completePointToIntegralCubic K n h i
local notation "V" => completePointOriginOpen K n h i
local notation "q" => completePointToOrigin K n h i

local notation "J" => completePointPulledOriginIdeal K n h i

/-- The original ideals agree on every affine chart in their common complement. -/
theorem completePointPulledOriginIdeal_complement_chart
    (A : (exactVeroneseProj K n h).affineOpens) (hA : A.1 ≤ (s).ker.support.compl) :
    (J).ideal A = (s).ker.ideal A := by
  have hJ : (J).comap
      (Scheme.Opens.ι (X := exactVeroneseProj K n h) (s).ker.support.compl) = ⊤ := by
    apply (Scheme.IdealSheafData.support_eq_bot_iff _).mp
    rw [Scheme.IdealSheafData.support_comap, completePointPulledOriginIdeal_support]
    ext x
    change (x.val ∈ (s).ker.support ↔ False)
    exact iff_false_intro x.property
  have hs := GlobalIdealPowerCompatibility.comap_complement (s).ker
  have he := congrArg (fun I => I.comap ((exactVeroneseProj K n h).homOfLE hA))
    (hJ.trans hs.symm)
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp,
    Scheme.homOfLE_ι] at he
  have ht := congrArg (fun I => I.ideal ⟨⊤, isAffineOpen_top A.1.toScheme⟩) he
  rw [Scheme.IdealSheafData.ideal_comap_ι_top,
    Scheme.IdealSheafData.ideal_comap_ι_top] at ht
  have hc := congrArg (Ideal.comap A.1.topIso.inv.hom) ht
  simpa only [Ideal.comap_map_of_bijective _
    (ConcreteCategory.bijective_of_isIso A.1.topIso.inv)] using hc

/-- The actual cubic-origin pullback is the original marking ideal, including multiplicity. -/
theorem completePointPulledOriginIdeal_eq_marking : (J) = (s).ker := by
  have he : ∀ x : exactVeroneseProj K n h,
      ∃ A : (exactVeroneseProj K n h).affineOpens,
        x ∈ A.1 ∧ (J).ideal A = (s).ker.ideal A := by
    intro x
    have hx : x ∈ completePointFirstOrderOpen K n h i ⊔ (s).ker.support.compl := by
      rw [completePointFirstOrderOpen_complement_cover]
      trivial
    rcases hx with hx | hx
    · obtain ⟨A, hxA, hA, hC⟩ :=
        (completePointFirstOrderCartier K n h i).exists_chart_le hx
      exact ⟨A, hxA, completePointPulledOriginIdeal_firstOrder_chart K n h i A hA hC⟩
    · obtain ⟨A, hxA, hA, _⟩ :=
        (completePointFirstOrderCartier K n h i).exists_chart_le hx
      exact ⟨A, hxA, completePointPulledOriginIdeal_complement_chart K n h i A hA⟩
  choose A hxA hA using he
  apply Scheme.IdealSheafData.ext_of_iSup_eq_top A _ hA
  apply top_unique
  intro x _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨x, hxA x⟩

end FLT.Mazur.PolygonInfinitesimalStages
