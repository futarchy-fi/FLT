/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantCyclicRelabel
public import FLT.Mazur.RelativeCyclicSubgroupComparison
public import FLT.Mazur.CompatibleSubgroupAmple

/-!
# Relabeling preserves the actual relative cyclic subgroup

The full curve stays fixed and the constant subgroup is permuted componentwise.
Compatibility with the whole-curve inclusion proves preservation of ampleness.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open UniversallyDistinctSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))
  (e : MulAut (Multiplicative (ZMod n)))

include hφ in
omit [NeZero n] in
/-- A permutation of cyclic labels preserves their universal distinctness. -/
theorem relativeCyclicMarking_relabel_distinct :
    UniversallyDistinct (fun i : ZMod n ↦ (φ.comp e.toMonoidHom) (.ofAdd i)) := by
  intro V g hV i j hij
  apply Multiplicative.ofAdd.injective
  apply e.injective
  have h := hφ V g hV (a₁ := (e (.ofAdd i)).toAdd) (a₂ := (e (.ofAdd j)).toAdd)
  exact congrArg Multiplicative.ofAdd (h (by
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ofAdd_toAdd] using hij))

/-- The relabeled subgroup retains the full original curve and actual subgroup inclusion. -/
def relativeCyclicSubgroupRelabelIso :
    FiniteSubgroup.CompatibleIso
      (E.relativeCyclicSubgroup (φ.comp e.toMonoidHom)
        (relativeCyclicMarking_relabel_distinct E φ hφ e))
      (E.relativeCyclicSubgroup φ hφ) where
  curve := Iso.refl E
  subgroup := ConstantCyclicRelabel.relabelIso S n e
  isMonHom := ConstantCyclicRelabel.relabel_isMonHom S n e
  compatible := by
    change (ConstantCyclicSectionMap.toScheme (φ.comp e.toMonoidHom) ≫ E.inclusion) ≫
      𝟙 E.curve = ConstantCyclicRelabel.relabel S n e ≫
        (ConstantCyclicSectionMap.toScheme φ ≫ E.inclusion)
    rw [Category.comp_id, ConstantCyclicRelabel.relabel_toScheme_assoc]

/-- Ampleness is unchanged by relabeling the actual cyclic sections. -/
theorem relativeCyclicSubgroup_relabel_isAmple_iff :
    (E.relativeCyclicSubgroup (φ.comp e.toMonoidHom)
      (relativeCyclicMarking_relabel_distinct E φ hφ e)).IsAmple ↔
        (E.relativeCyclicSubgroup φ hφ).IsAmple :=
  (relativeCyclicSubgroupRelabelIso E φ hφ e).isAmple_iff

end FLT.Mazur.GeneralizedEllipticCurve
