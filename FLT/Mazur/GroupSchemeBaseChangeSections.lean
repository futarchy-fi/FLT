/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupSchemeBaseChangeComparison
public import FLT.Mazur.OverPullbackSection

/-!
# Group morphisms retain actual pullback sections

A section comparison pulls back along any source map. The statement is proved
for abstract group objects to keep geometric group-law definitions sealed when
it is specialized to concrete curve families.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GroupSchemeBaseChange
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S T : Scheme.{u}} (f : T ⟶ S) {G H : CommGrp (Over S)}

/-- Any group-section comparison remains an equality of the actual pullback sections. -/
theorem lift_map_eq (e : G ⟶ H) (p : Over.mk f ⟶ G.X) (q : Over.mk f ⟶ H.X)
    (h : p ≫ e.hom.hom.hom = q) :
    OverPullbackSection.lift f G.X p ≫
      ((Over.pullback f).mapCommGrp.map e).hom.hom.hom =
        OverPullbackSection.lift f H.X q :=
  (OverPullbackSection.lift_map f G.X e.hom.hom.hom p).trans
    (congrArg (OverPullbackSection.lift f H.X) h)

end FLT.Mazur.GroupSchemeBaseChange
