/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassAuxiliarySchemeMarking
public import FLT.Mazur.UniversalWeierstrassAuxiliaryTorsionCover

/-!
# Full auxiliary labels on the actual geometric pullback family

Every four-torsion section of the original pulled-back group has exactly one
auxiliary label. The proof factors its actual scheme map through the full
torsion comparison, so it retains the original parameter and group section.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.UniversalWeierstrass
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [IsAlgClosed K] (f : Spec (.of K) ⟶ levelFour.left)

/-- All torsion sections in the actual geometric family have unique original auxiliary labels. -/
theorem auxiliarySchemeMarking_geometric_full
    (P : 𝟙_ (Over (Spec (.of K))) ⟶ (auxiliarySchemeGroup f).X) (hP : P ^ 4 = 1) :
    ∃! a : Labels 4, auxiliarySchemeMarking f a = P := by
  let e := GroupMarkingBaseChange.pointsMulEquiv (f ≫ levelFour.hom)
    universalGroup (𝟙_ (Over (Spec (.of K))))
  let p := e.symm P
  have hp : p ^ 4 = 1 := by
    change (e.symm P) ^ 4 = 1
    rw [← map_pow, hP, map_one]
  let t := GroupTorsionScheme.lift universalGroup 4 p hp
  let k : Spec (.of K) ⟶ auxiliaryFourTorsion := pullback.lift t.left f (by
    exact t.w.trans (Category.id_comp _))
  obtain ⟨a, q, hq⟩ := auxiliaryTorsionSection_geometric_factor K k
  have hqf : q = f := by
    have h := congrArg (· ≫ auxiliaryFourTorsionMap) hq
    rw [Category.assoc, auxiliaryTorsionSection_map, Category.comp_id] at h
    simpa only [k, auxiliaryFourTorsionMap, pullback.lift_snd] using h
  subst q
  have hm : f ≫ (auxiliaryMarking 4 a).left = p.left := by
    have h := congrArg (fun z ↦ z ≫ pullback.fst fourTorsion.hom levelFour.hom ≫
      (GroupTorsionScheme.inclusion universalGroup 4).left) hq
    simpa only [Category.assoc, auxiliaryTorsionSection_fst_assoc, k,
      pullback.lift_fst_assoc, ← Over.comp_left, auxiliaryTorsionMarking_inclusion,
      t, GroupTorsionScheme.lift_inclusion] using h
  have ha : auxiliarySchemeMarking f a = P := by
    apply e.symm.injective
    change e.symm (e _) = p
    rw [e.symm_apply_apply]
    apply Over.OverMorphism.ext
    exact hm
  exact ⟨a, ha, fun b hb ↦ auxiliarySchemeMarking_injective f (hb.trans ha.symm)⟩

end FLT.Mazur.UniversalWeierstrass
