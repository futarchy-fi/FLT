/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGroupSectionComposition
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Arbitrary full section markings under base change

All label homomorphisms pull back using the actual section map. This keeps
independent auxiliary markings available on the original generator cover.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
universe v
variable {S T : Scheme} {L : Type v} [Monoid L] (g : T ⟶ S)
  (E : GeneralizedEllipticCurve S) (m : L →* (𝟙_ (Over S) ⟶ E.group))

/-- Pull back all labels of any original group-valued section marking. -/
def pullMarking : L →* (𝟙_ (Over T) ⟶ (E.baseChange g).group) where
  toFun j := pullSection g (m j)
  map_one' := by simp only [map_one, pullSection, Functor.map_one, comp_one]
  map_mul' i j := by simp only [map_mul, pullSection, Functor.map_mul, comp_mul]

/-- Every original label is preserved after projecting the actual pullback section. -/
@[reassoc] theorem pullMarking_fst (j : L) :
    (pullMarking g E m j).left ≫ pullback.fst E.group.hom g = g ≫ (m j).left :=
  section_fst g (m j)

/-- Pullback commutes with arbitrary relabeling of a complete marking. -/
theorem pullMarking_comp {K : Type v} [Monoid K] (r : K →* L) :
    pullMarking g E (m.comp r) = (pullMarking g E m).comp r := rfl

/-- The full curve composition comparison retains each pulled auxiliary label. -/
theorem pullMarking_compEq {U : Scheme} (k : U ⟶ T) (f : U ⟶ S) (w : f = k ≫ g)
    (j : L) :
    pullMarking f E m j ≫ (E.baseChangeCompEqIso g k f w).hom.group =
      pullMarking k (E.baseChange g) (pullMarking g E m) j :=
  E.baseChangeCompEqIso_groupSection g k f w (m j)

end FLT.Mazur.GroupSectionBaseChange
