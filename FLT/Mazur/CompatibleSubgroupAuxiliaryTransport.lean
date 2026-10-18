/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CompatibleSubgroupGroupSectionComposition

/-!
# Independent auxiliary frames through original subgroup comparisons

Transport a full label homomorphism using only a given original comparison.
Faithfulness is preserved, and a later atlas comparison can be proved to
retain this independently transported frame.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
open GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} {n : ℕ} {E F G : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n} {K : G.FiniteSubgroup n}
  {L : Type} [Monoid L] (a : CompatibleIso H J)
  (m : L →* (𝟙_ (Over S) ⟶ E.group))

/-- Transport an independently specified frame through the original group comparison. -/
def CompatibleIso.transportAuxiliary : L →* (𝟙_ (Over S) ⟶ F.group) where
  toFun i := m i ≫ a.curve.hom.group
  map_one' := by rw [map_one, one_comp]
  map_mul' i j := by rw [map_mul, mul_comp]

/-- The transported label is its actual original group section followed by the comparison. -/
theorem CompatibleIso.transportAuxiliary_apply (i : L) :
    a.transportAuxiliary m i = m i ≫ a.curve.hom.group := rfl

/-- Faithfulness is preserved and reflected by the full original comparison. -/
theorem CompatibleIso.transportAuxiliary_injective_iff :
    Function.Injective (a.transportAuxiliary m) ↔ Function.Injective m := by
  constructor
  · intro hm i j hij
    exact hm (congrArg (· ≫ a.curve.hom.group) hij)
  · intro hm i j hij
    apply hm
    have hi : a.curve.hom.group ≫ a.curve.inv.group = 𝟙 _ :=
      congrArg Hom.group a.curve.hom_inv_id
    have he := congrArg (· ≫ a.curve.inv.group) hij
    simpa only [CompatibleIso.transportAuxiliary_apply, Category.assoc, hi,
      Category.comp_id] using he

/-- Transport through two comparisons agrees on every label with their composite. -/
theorem CompatibleIso.transportAuxiliary_trans (b : CompatibleIso J K) :
    (a.trans b).transportAuxiliary m = b.transportAuxiliary (a.transportAuxiliary m) := by
  apply MonoidHom.ext
  intro i
  change m i ≫ (a.curve.hom.group ≫ b.curve.hom.group) =
    (m i ≫ a.curve.hom.group) ≫ b.curve.hom.group
  rw [Category.assoc]

/-- An ambient section equation survives base change of the full compatible comparison. -/
theorem CompatibleIso.baseChange_group_section {T : Scheme} (g : T ⟶ S)
    (s : 𝟙_ (Over S) ⟶ E.group) (t : 𝟙_ (Over S) ⟶ F.group)
    (h : s ≫ a.curve.hom.group = t) :
    pullSection g s ≫ (a.baseChange g).curve.hom.group = pullSection g t := by
  change pullSection g s ≫ (Over.pullback g).map a.curve.hom.group = _
  rw [← section_comp, h]

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
