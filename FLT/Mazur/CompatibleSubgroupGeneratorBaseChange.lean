/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupIsoBaseChange
public import FLT.Mazur.GroupSectionBaseChange

/-!
# Specified subgroup sections under compatible base change

The canonical direct-versus-iterated comparison retains the original section.
A pulled compatible isomorphism also retains any prescribed section equality.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T U : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  (H : E.FiniteSubgroup n) (g : T ⟶ S) (k : U ⟶ T)
  (P : 𝟙_ (Over S) ⟶ H.carrier)

/-- The direct section becomes the iterated section under the canonical compatible comparison. -/
theorem compatibleBaseChangeComp_section :
    pullSection (k ≫ g) P ≫ (compatibleBaseChangeComp H g k).subgroup.hom =
      pullSection k (pullSection g P) := by
  change pullSection (k ≫ g) P ≫ (Over.pullbackComp k g).hom.app H.carrier = _
  simpa only [pullSection, Functor.comp_map, Functor.LaxMonoidal.comp_ε,
    Functor.map_comp, Category.assoc] using
      MonoidalActionMap.unit_naturality P (Over.pullbackComp k g).hom

/-- The inverse comparison recovers the section on the direct pullback. -/
theorem compatibleBaseChangeComp_inv_section :
    pullSection k (pullSection g P) ≫ (compatibleBaseChangeComp H g k).subgroup.inv =
      pullSection (k ≫ g) P := by
  rw [← compatibleBaseChangeComp_section H g k P, Category.assoc,
    Iso.hom_inv_id, Category.comp_id]

variable {H} {J : F.FiniteSubgroup n} (a : CompatibleIso H J)

/-- A section equality survives the actual base change of the full compatible isomorphism. -/
theorem CompatibleIso.baseChange_section (Q : 𝟙_ (Over S) ⟶ J.carrier)
    (h : P ≫ a.subgroup.hom = Q) :
    pullSection g P ≫ (a.baseChange g).subgroup.hom = pullSection g Q := by
  change pullSection g P ≫ (Over.pullback g).map a.subgroup.hom = _
  rw [← section_comp, h]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
