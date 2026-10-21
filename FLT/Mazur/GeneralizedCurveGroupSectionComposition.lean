/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq
public import FLT.Mazur.GroupSectionBaseChange
public import FLT.Mazur.OverPullbackSectionComposition

/-!
# Full group sections under equal composite base change

The actual group comparison carries each direct section to its iterated
pullback. The equality is on the entire smooth group, without distinctness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} (E : GeneralizedEllipticCurve S)
  (g : T ⟶ S) (k : U ⟶ T)

/-- The full group comparison retains every section under composition. -/
theorem baseChangeCompIso_groupSection (p : 𝟙_ (Over S) ⟶ E.group) :
    pullSection (k ≫ g) p ≫ (E.baseChangeCompIso g k).hom.group =
      pullSection k (pullSection g p) := by
  let e := (Over.pullbackComp k g).app E.group
  change pullSection (k ≫ g) p ≫ e.hom = _
  apply (cancel_mono e.inv).mp
  rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  apply OverPullbackSection.hom_ext
  simp only [Over.comp_left, Category.assoc, e, Iso.app_inv,
    OverPullbackSection.comp_inv_fst, section_fst, section_fst_assoc]

/-- Equal composite base maps retain every original group section as well. -/
theorem baseChangeCompEqIso_groupSection (f : U ⟶ S) (w : f = k ≫ g)
    (p : 𝟙_ (Over S) ⟶ E.group) :
    pullSection f p ≫ (E.baseChangeCompEqIso g k f w).hom.group =
      pullSection k (pullSection g p) := by
  subst f
  change pullSection (k ≫ g) p ≫ (𝟙 _ ≫ (E.baseChangeCompIso g k).hom.group) = _
  rw [Category.id_comp]
  exact E.baseChangeCompIso_groupSection g k p

end FLT.Mazur.GeneralizedEllipticCurve
