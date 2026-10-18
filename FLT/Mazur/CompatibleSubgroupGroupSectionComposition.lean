/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupGeneratorBaseChange

/-!
# Auxiliary group sections through compatible subgroup comparisons

Compose section equalities on the ambient group families, so applications to
normalization and relabeling need not unfold geometric group constructions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {n : ℕ} {E F G K : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}
  {A : G.FiniteSubgroup n} {B : K.FiniteSubgroup n}
  (a : CompatibleIso H J) (b : CompatibleIso J A) (c : CompatibleIso A B)

/-- Two full comparisons retain the stated ambient group section. -/
theorem CompatibleIso.group_section_trans
    (s : 𝟙_ (Over S) ⟶ E.group) (t : 𝟙_ (Over S) ⟶ F.group)
    (u : 𝟙_ (Over S) ⟶ G.group)
    (ha : s ≫ a.curve.hom.group = t) (hb : t ≫ b.curve.hom.group = u) :
    s ≫ (a.trans b).curve.hom.group = u := by
  change s ≫ (a.curve.hom.group ≫ b.curve.hom.group) = u
  rw [← Category.assoc, ha, hb]

/-- The inverse full comparison recovers the original ambient group section. -/
theorem CompatibleIso.group_section_symm
    (s : 𝟙_ (Over S) ⟶ E.group) (t : 𝟙_ (Over S) ⟶ F.group)
    (ha : s ≫ a.curve.hom.group = t) : t ≫ a.symm.curve.hom.group = s := by
  change t ≫ a.curve.inv.group = s
  rw [← ha, Category.assoc]
  have hi : a.curve.hom.group ≫ a.curve.inv.group = 𝟙 _ :=
    congrArg Hom.group a.curve.hom_inv_id
  rw [hi, Category.comp_id]

/-- Three full comparisons carry the original specified section to the final specified section. -/
theorem CompatibleIso.group_section_trans_three
    (s : 𝟙_ (Over S) ⟶ E.group) (t : 𝟙_ (Over S) ⟶ F.group)
    (u : 𝟙_ (Over S) ⟶ G.group) (v : 𝟙_ (Over S) ⟶ K.group)
    (ha : s ≫ a.curve.hom.group = t) (hb : t ≫ b.curve.hom.group = u)
    (hc : u ≫ c.curve.hom.group = v) :
    s ≫ (a.trans (b.trans c)).curve.hom.group = v := by
  change s ≫ (a.curve.hom.group ≫ b.curve.hom.group ≫ c.curve.hom.group) = v
  rw [← Category.assoc, ha, ← Category.assoc, hb, hc]

/-- Equality of full comparisons transfers a section equation without unfolding comparisons. -/
theorem CompatibleIso.group_section_iso_congr (d : CompatibleIso H J)
    (s : 𝟙_ (Over S) ⟶ E.group) (t : 𝟙_ (Over S) ⟶ F.group)
    (had : a = d) (hd : s ≫ d.curve.hom.group = t) : s ≫ a.curve.hom.group = t := by
  rw [had]
  exact hd

open GroupSectionBaseChange

/-- Direct auxiliary group sections become iterated sections under compatible pullback. -/
theorem compatibleBaseChangeComp_group_section {T U : Scheme} (H : E.FiniteSubgroup n)
    (g : T ⟶ S) (k : U ⟶ T) (P : 𝟙_ (Over S) ⟶ E.group) :
    pullSection (k ≫ g) P ≫ (compatibleBaseChangeComp H g k).curve.hom.group =
      pullSection k (pullSection g P) := by
  change pullSection (k ≫ g) P ≫ (Over.pullbackComp k g).hom.app E.group = _
  simpa only [pullSection, Functor.comp_map, Functor.LaxMonoidal.comp_ε,
    Functor.map_comp, Category.assoc] using
      MonoidalActionMap.unit_naturality P (Over.pullbackComp k g).hom

/-- The inverse comparison recovers the auxiliary section on the direct pullback. -/
theorem compatibleBaseChangeComp_inv_group_section {T U : Scheme} (H : E.FiniteSubgroup n)
    (g : T ⟶ S) (k : U ⟶ T) (P : 𝟙_ (Over S) ⟶ E.group) :
    pullSection k (pullSection g P) ≫ (compatibleBaseChangeComp H g k).curve.inv.group =
      pullSection (k ≫ g) P := by
  rw [← compatibleBaseChangeComp_group_section H g k P, Category.assoc]
  have hi : (compatibleBaseChangeComp H g k).curve.hom.group ≫
      (compatibleBaseChangeComp H g k).curve.inv.group = 𝟙 _ :=
    congrArg Hom.group (compatibleBaseChangeComp H g k).curve.hom_inv_id
  rw [hi]
  exact Category.comp_id _

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
