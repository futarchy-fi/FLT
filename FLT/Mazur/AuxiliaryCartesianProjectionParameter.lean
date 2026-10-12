/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AuxiliaryBaseProjectionParameter
public import FLT.Mazur.AuxiliaryLevelGroupTransport

/-!
# Full faithful parameters through a cartesian group comparison

A group isomorphism followed by the actual inverse pullback adjunction projects
all labels to the original coefficient group. Evaluation records the exact
scheme map for every label on every test.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.AuxiliaryLevel
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme} (g : T ⟶ S) (G : CommGrp (Over S)) (H : CommGrp (Over T))
  [IsSeparated G.X.hom] [IsSeparated H.X.hom]
  (e : H ≅ (Over.pullback g).mapCommGrp.obj G) (A : Type) [Group A] [Fintype A]

/-- The actual coefficient pullback remains separated. -/
local instance : IsSeparated ((Over.pullback g).mapCommGrp.obj G).X.hom :=
  inferInstanceAs (IsSeparated (pullback.snd G.X.hom g))

/-- Project the complete original faithful parameter through its cartesian group comparison. -/
def cartesianProjectionParameter {U : Over T} (f : U ⟶ faithfulScheme H.X A) :
    (Over.map g).obj U ⟶ faithfulScheme G.X A :=
  baseProjectionParameter g G.X A
    (groupTransportParameter H ((Over.pullback g).mapCommGrp.obj G) e A f)

/-- Each label projects by the specified group comparison and actual pullback projection. -/
theorem cartesianProjectionParameter_value_left {U : Over T}
    (f : U ⟶ faithfulScheme H.X A) (a : A) :
    (cartesianProjectionParameter g G H e A f ≫ faithfulInclusion G.X A ≫
      value G.X A a).left =
        (f ≫ faithfulInclusion H.X A ≫ value H.X A a).left ≫
          e.hom.hom.hom.hom.left ≫ pullback.fst G.X.hom g := by
  rw [cartesianProjectionParameter, baseProjectionParameter_value_left]
  change (groupTransportParameter H ((Over.pullback g).mapCommGrp.obj G) e A f ≫
    faithfulInclusion ((Over.pullback g).mapCommGrp.obj G).X A ≫
    value ((Over.pullback g).mapCommGrp.obj G).X A a).left ≫ _ = _
  rw [groupTransportParameter_value, Over.comp_left, Category.assoc]
  rfl

end FLT.Mazur.AuxiliaryLevel
