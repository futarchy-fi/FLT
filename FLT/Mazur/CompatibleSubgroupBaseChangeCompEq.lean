/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIsoBaseChange
public import FLT.Mazur.GeneralizedCurveBaseChangeCompEq
public import FLT.Mazur.GeneralizedCurveSectionComposition

/-!
# Compatible subgroup comparison for equal composite base maps

The direct and iterated pullbacks retain the full DR curve, the actual
subgroup inclusion, and each original subgroup section.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} {n : ℕ} {E : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (g : T ⟶ S) (k : U ⟶ T)
  (f : U ⟶ S) (w : f = k ≫ g)

/-- Equal composite base maps give a comparison of the actual finite subgroup data. -/
def compatibleBaseChangeCompEq :
    CompatibleIso (H.baseChange f) ((H.baseChange g).baseChange k) := by
  subst f
  exact compatibleBaseChangeComp H g k

/-- The compatible comparison uses the full equal-composite DR comparison. -/
theorem compatibleBaseChangeCompEq_curve :
    (compatibleBaseChangeCompEq H g k f w).curve = E.baseChangeCompEqIso g k f w := by
  subst f
  change E.baseChangeCompIso g k = (Iso.refl _).trans (E.baseChangeCompIso g k)
  exact (Iso.refl_trans _).symm

/-- The composition comparison carries each direct section to its iterated pullback. -/
theorem compatibleBaseChangeComp_section (P : 𝟙_ (Over S) ⟶ H.carrier) :
    pullSection (k ≫ g) P ≫ (compatibleBaseChangeComp H g k).subgroup.hom =
      pullSection k (pullSection g P) := by
  let e := (Over.pullbackComp k g).app H.carrier
  change pullSection (k ≫ g) P ≫ e.hom = _
  apply (cancel_mono e.inv).mp
  rw [Category.assoc, e.hom_inv_id, Category.comp_id]
  apply Over.OverMorphism.ext
  apply pullback.hom_ext
  · simp only [Over.comp_left, Category.assoc, e, Iso.app_inv,
      OverPullbackSection.comp_inv_fst, section_fst, section_fst_assoc]
  · exact (pullSection (k ≫ g) P).w.trans
      ((pullSection k (pullSection g P)) ≫ e.inv).w.symm

/-- The equal-composite comparison preserves every original subgroup section. -/
theorem compatibleBaseChangeCompEq_section (P : 𝟙_ (Over S) ⟶ H.carrier) :
    pullSection f P ≫ (compatibleBaseChangeCompEq H g k f w).subgroup.hom =
      pullSection k (pullSection g P) := by
  subst f
  exact compatibleBaseChangeComp_section H g k P

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
