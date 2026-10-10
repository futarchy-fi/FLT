/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperStageBaseChangeLimit
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# The original residue fiber as a proper-stage limit

Use the standard fiber convention, whose first pullback factor is the original
scheme. Pullback symmetry supplies its cone to the base-changed stage diagram.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {S : Scheme.{u}} {D : I ⥤ Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (i : I)
  (c : Cone D) (b : c.pt ⟶ S) (hb : ∀ j, c.π.app j ≫ t.app j = b) (s : S)

/-- The standard residue fiber cones to every base-changed refinement of the chosen stage. -/
def properStageResidueFiberCone :
    Cone (properStageBaseChangeDiagram t (S.fromSpecResidueField s) i) :=
  (properStageBaseChangeCone t (S.fromSpecResidueField s) i c b hb).extend
    (pullbackSymmetry b (S.fromSpecResidueField s)).hom

omit [IsCofiltered I] in
/-- Its cone point is the actual residue fiber of the original structure map. -/
theorem properStageResidueFiberCone_pt :
    (properStageResidueFiberCone t i c b hb s).pt = b.fiber s := rfl

/-- The original residue fiber is the inverse limit of the proper-stage fiber system. -/
def properStageResidueFiberIsLimit (hc : IsLimit c) :
    IsLimit (properStageResidueFiberCone t i c b hb s) :=
  (properStageBaseChangeIsLimit t (S.fromSpecResidueField s) i c hc b hb).extendIso _

omit [IsCofiltered I] in
/-- Closed original projections remain closed on the standard residue fiber. -/
theorem properStageResidueFiberCone_closed (j : Over i)
    [IsClosedImmersion (c.π.app j.left)] :
    IsClosedImmersion ((properStageResidueFiberCone t i c b hb s).π.app j) := by
  let _ : IsClosedImmersion ((c.whisker (Over.forget i)).π.app j) :=
    inferInstanceAs (IsClosedImmersion (c.π.app j.left))
  let _ : IsClosedImmersion
      ((properStageBaseChangeCone t (S.fromSpecResidueField s) i c b hb).π.app j) :=
    schemeBaseChangeCone_app_isClosedImmersion ((Over.forget i).whiskerLeft t)
      (S.fromSpecResidueField s) (c.whisker (Over.forget i)) b (fun j ↦ hb j.left) j
  change IsClosedImmersion ((pullbackSymmetry b (S.fromSpecResidueField s)).hom ≫ _)
  infer_instance

end FLT.Mazur.Approximation
