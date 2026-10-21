/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryLevelBaseChangeRelabel
public import FLT.Mazur.AuxiliaryLevelFaithfulBaseChange
public import FLT.Mazur.CyclicBoundaryProjectionFaithfulness

/-!
# Actual boundary marking parameters under arbitrary base change

The full parameter comparison retains the cyclic projection and the common
finite action. Faithfulness of the cyclic projection is preserved and reflected
on every relative test; no smoothness of the original whole curve is used.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.CyclicBoundaryParameter
open AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (E : Over S) [GrpObj E] (n : ℕ) [NeZero n]

/-- The original boundary equation scheme over the actual new base. -/
def parameterBaseChangeIso :
    (Over.pullback g).obj (parameter E n) ≅ parameter ((Over.pullback g).obj E) n :=
  homSchemeBaseChangeIso g E (Label n)

/-- The actual comparison preserves restriction to the cyclic labels. -/
@[reassoc] theorem parameterBaseChange_cyclicProjection :
    (parameterBaseChangeIso g E n).hom ≫ cyclicProjection ((Over.pullback g).obj E) n =
      (Over.pullback g).map (cyclicProjection E n) ≫
        (homSchemeBaseChangeIso g E (Multiplicative (ZMod n))).hom := by
  apply homScheme_ext
  intro a
  change (homSchemeBaseChangeHom g E (Label n) ≫ cyclicProjection _ n) ≫ value _ _ a =
    ((Over.pullback g).map (cyclicProjection E n) ≫
      homSchemeBaseChangeHom g E _) ≫ value _ _ a
  rw [Category.assoc, cyclicProjection_value, homSchemeBaseChangeHom_value,
    Category.assoc, homSchemeBaseChangeHom_value, ← Functor.map_comp, cyclicProjection_value]

/-- Every independent auxiliary and cyclic relabeling commutes with base change. -/
@[reassoc] theorem parameterBaseChange_action (e : CyclicCharacteristicAtlas.RelabelGroup n) :
    (parameterBaseChangeIso g E n).hom ≫ (action ((Over.pullback g).obj E) n e).hom =
      (Over.pullback g).map (action E n e).hom ≫ (parameterBaseChangeIso g E n).hom :=
  homSchemeBaseChange_action g E (labelAction n e)

/-- Cyclic faithfulness is preserved and reflected over every relative test scheme. -/
theorem parameterBaseChange_faithful_iff {U : Over T}
    (q : U ⟶ (Over.pullback g).obj (parameter E n)) :
    UniversallyFaithful ((Over.pullback g).obj E) (Multiplicative (ZMod n))
      ((q ≫ (parameterBaseChangeIso g E n).hom) ≫
        cyclicProjection ((Over.pullback g).obj E) n) ↔
    UniversallyFaithful E (Multiplicative (ZMod n))
      ((((Over.mapPullbackAdj g).homEquiv U _).symm q) ≫ cyclicProjection E n) := by
  rw [Category.assoc, parameterBaseChange_cyclicProjection, ← Category.assoc,
    homSchemeBaseChange_faithful_iff, Adjunction.homEquiv_naturality_right_symm]

end FLT.Mazur.CyclicBoundaryParameter
