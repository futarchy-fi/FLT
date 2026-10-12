/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierGeneratorMarkedSubgroup
public import FLT.Mazur.GeneralizedCurveCyclicMarkingBaseChange

/-!
# Cartier markings of retained subgroups

Transport keeps the actual subgroup carrier. Pullback and full-curve transport
preserve its Cartier generator and every cyclic label without etaleness.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} {E F : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n) (e : E ≅ F)

/-- Transport changes the curve embedding and retains the actual subgroup carrier. -/
def transportCompatibleIso : CompatibleIso H (H.transport e) where
  curve := e
  subgroup := Iso.refl H.carrier
  isMonHom := inferInstanceAs (IsMonHom (𝟙 H.carrier))
  compatible := by rw [Iso.refl_hom, Category.id_comp, transport_curveMap]

/-- The identical generator section remains Cartier after full curve transport. -/
theorem transport_cartierGenerator {P : 𝟙_ (Over S) ⟶ H.carrier}
    (hP : H.IsCartierGenerator P) : (H.transport e).IsCartierGenerator P := by
  simpa only [transportCompatibleIso, Iso.refl_hom, Category.comp_id] using
    (H.transportCompatibleIso e).cartierGenerator hP

variable [NeZero n] {P : 𝟙_ (Over S) ⟶ H.carrier} (hP : H.IsCartierGenerator P)

/-- Transport retains each original cyclic section after the given group isomorphism. -/
theorem generatorCurveMarking_transport (i : Multiplicative (ZMod n)) :
    (H.transport e).generatorCurveMarking (H.transport_cartierGenerator e hP) i =
      H.generatorCurveMarking hP i ≫ e.hom.group := by
  change (P ^ i.toAdd.val) ≫ (H.inclusion ≫ e.hom.group) =
    ((P ^ i.toAdd.val) ≫ H.inclusion) ≫ e.hom.group
  exact (Category.assoc _ _ _).symm

/-- Every original generator label pulls back to the label of its pulled Cartier generator. -/
theorem generatorCurveMarking_baseChange (g : T ⟶ S) (i : Multiplicative (ZMod n)) :
    (H.baseChange g).generatorCurveMarking (hP.baseChange H g) i =
      pullCyclicMarking (E := E) g (H.generatorCurveMarking hP) i := by
  change (GroupSectionBaseChange.pullSection g P ^ i.toAdd.val) ≫
    (Over.pullback g).map H.inclusion =
      GroupSectionBaseChange.pullSection g ((P ^ i.toAdd.val) ≫ H.inclusion)
  rw [GroupSectionBaseChange.section_comp, GroupSectionBaseChange.section_pow]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
