/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GroupMarkingBaseChangeInverse

/-!
# A sealed pullback adjunction for bundled group schemes

The equivalence is stated using the bundled pulled-back group. Its projection
formula allows geometric callers to use the adjunction without expanding their
constructed group laws while comparing bundled and unbundled group structures.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj
namespace FLT.Mazur.GroupSchemePointAdjunction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {S T : Scheme.{u}} (s : T ⟶ S) (G : CommGrp (Over S)) (U : Over T)

/-- The actual pullback adjunction as an equivalence of group-valued test morphisms. -/
irreducible_def pointsEquiv : ((Over.map s).obj U ⟶ G.X) ≃*
    (U ⟶ ((Over.pullback s).mapCommGrp.obj G).X) :=
  GroupMarkingBaseChange.pointsMulEquiv s G.X U

/-- The inverse equivalence retains the first projection of the actual fiber product. -/
theorem pointsEquiv_symm_left (x : U ⟶ ((Over.pullback s).mapCommGrp.obj G).X) :
    ((pointsEquiv s G U).symm x).left = x.left ≫ pullback.fst G.X.hom s := by
  rw [pointsEquiv_def]
  exact GroupMarkingBaseChange.pointsMulEquiv_symm_left s G.X U x

/-- The forward equivalence also retains the original scheme morphism. -/
@[reassoc] theorem pointsEquiv_fst (x : (Over.map s).obj U ⟶ G.X) :
    (pointsEquiv s G U x).left ≫ pullback.fst G.X.hom s = x.left := by
  rw [← pointsEquiv_symm_left, MulEquiv.symm_apply_apply]

end FLT.Mazur.GroupSchemePointAdjunction
