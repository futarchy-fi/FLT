/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteCyclicDivisor
public import FLT.Mazur.PolygonCompleteClosedPointLineComparison
public import FLT.Mazur.ConstantCyclicInclusion
public import FLT.Mazur.PolygonActionSmooth

/-!
# The original complete cyclic divisor in the closed smooth group

On the original closed square, the complete-family finite marking map is
exactly the all-one subgroup of the polygon's full smooth group. Consequently
the actual complete product divisor inclusion is a group homomorphism there.
The full smooth group over the complete coefficient base is not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonPinching
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] cyclic_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "P" => PolygonCyclicAtlas.normalization K n h
local notation "Q" => PolygonCyclicAtlas.nodes K n h
local notation "hn" => (Nat.lt_of_lt_of_le (Nat.succ_pos 1) h)
local notation "hp" => PolygonCyclicPushout.isPushout K n h hn
local notation "b" => completeClosedBase K
local notation "j" => completeClosedFiberInclusion K n h
local notation "q" => PolygonCyclicAtlas.toBase K n h
local notation "hb" => completeClosedFiber_isPullback K n h

omit [NeZero n] in
/-- Local finite presentation on the original polygon as an object over the field. -/
theorem completeClosedPolygon_lfp :
    LocallyOfFinitePresentation (PolygonCyclicAtlas.polygon K n h).hom :=
  cyclic_lfp K n h

attribute [local instance] completeClosedPolygon_lfp

/-- The original closed finite marking map is the all-one inclusion in the full smooth group. -/
theorem completeSmoothCyclicMarking_closed_eq :
    completeSmoothCyclicMarking K n h b j q hb =
      ConstantCyclicInclusion.inclusion K n ≫ (smoothIso K n hn P Q hp).inv := by
  apply Sigma.hom_ext
  intro a
  change ConstantCyclicGroup.component (Spec (.of K)) n a ≫ _ = _
  rw [ConstantCyclicInclusion.component_inclusion_assoc]
  apply Over.OverMorphism.ext
  apply (cancel_mono (q).smoothLocus.ι).mp
  calc
    _ = PolygonMarkedSections.sectionMap K n P 1 ((ZMod.finEquiv n).symm a) := by
      rw [show ConstantCyclicGroup.component (Spec (.of K)) n a ≫
          completeSmoothCyclicMarking K n h b j q hb = _ from Sigma.ι_comp_desc _ a]
      change completeSmoothCartesianMarking K n h b j q hb _ ≫ _ = _
      rw [completeSmoothCartesianMarking_ι, completeCartesianMarking_closed]
    _ = _ := by
      have he := component_smoothIso_inv K n hn P Q hp ((ZMod.finEquiv n).symm a)
      simp only [RingEquiv.apply_symm_apply] at he
      have he' := congrArg (fun f ↦ ProjectiveLineActionSpecialization.unitPoint K 1 ≫ f) he
      simpa only [Over.comp_left, Category.assoc, PolygonMarkedSections.sectionMap,
        ProjectiveLineActionSpecialization.identity_left, PolygonSplitGroup.component,
        PolygonCyclicAtlas.polygon, Over.mk_hom] using he'.symm

/-- The constructed full closed smooth group, on the exact complete-square carrier. -/
abbrev completeClosedSmoothGrpObj : GrpObj (Over.mk ((q).smoothLocus.ι ≫ q)) :=
  smoothGrpObj K n hn P Q hp

/-- The actual original marking scheme preserves multiplication in the full closed smooth group. -/
theorem completeSmoothCyclicMarking_closed_isMonHom :
    let _ := completeClosedSmoothGrpObj K n h
    IsMonHom (completeSmoothCyclicMarking K n h b j q hb) := by
  let _ := completeClosedSmoothGrpObj K n h
  change IsMonHom (completeSmoothCyclicMarking K n h b j q hb)
  rw [completeSmoothCyclicMarking_closed_eq]
  let _ := smoothGrpObj K n hn P Q hp
  let _ : IsMonHom (smoothIso K n hn P Q hp).inv :=
    isMonHom_ofIso (smoothIso K n hn P Q hp).symm
  exact inferInstanceAs
    (IsMonHom (ConstantCyclicInclusion.inclusion K n ≫ (smoothIso K n hn P Q hp).inv))

/-- The original product divisor inclusion preserves the full closed smooth group law. -/
theorem completeCyclicDivisorSmoothMap_closed_isMonHom :
    let _ := completeCyclicDivisorGrpObj K n h b j q hb
    let _ := completeClosedSmoothGrpObj K n h
    IsMonHom (completeCyclicDivisorSmoothMap K n h b j q hb) := by
  let _ := completeCyclicDivisorGrpObj K n h b j q hb
  let _ := completeClosedSmoothGrpObj K n h
  let _ := completeSmoothCyclicMarking_closed_isMonHom K n h
  change IsMonHom (completeCyclicDivisorSmoothMap K n h b j q hb)
  dsimp only [completeCyclicDivisorSmoothMap]
  infer_instance

end FLT.Mazur.PolygonInfinitesimalStages
