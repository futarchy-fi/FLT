/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.CategoryTheory.Monoidal.Cartesian.Over
public import Mathlib.CategoryTheory.Monoidal.Cartesian.CommGrp_

/-!
# Full group-valued markings under the actual pullback adjunction

The adjunction between composition and pullback identifies all relative points
as groups. It therefore transports complete label homomorphisms, on arbitrary
test schemes, while retaining their original scheme maps after projection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open scoped CategoryTheory.Obj

namespace FLT.Mazur.GroupMarkingBaseChange

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v
variable {S T : Scheme.{u}} (g : T ⟶ S) (G : Over S) [MonObj G] (U : Over T)
  {L : Type v} [Monoid L]

/-- The actual pullback adjunction preserves multiplication on all relative points. -/
def pointsMulEquiv : ((Over.map g).obj U ⟶ G) ≃* (U ⟶ (Over.pullback g).obj G) where
  __ := (Over.mapPullbackAdj g).homEquiv U G
  map_mul' x y := by
    change (Over.mapPullbackAdj g).homEquiv U G (x * y) =
      (Over.mapPullbackAdj g).homEquiv U G x * (Over.mapPullbackAdj g).homEquiv U G y
    simp only [Adjunction.homEquiv_apply, Functor.map_mul, MonObj.comp_mul]

/-- Projection of the pulled-back relative point is its original scheme morphism. -/
@[reassoc] theorem pointsMulEquiv_fst (p : (Over.map g).obj U ⟶ G) :
    (pointsMulEquiv g G U p).left ≫ pullback.fst G.hom g = p.left := by
  change ((Over.mapPullbackAdj g).homEquiv U G p).left ≫ _ = _
  rw [Adjunction.homEquiv_apply]
  simp only [Over.comp_left, Over.pullback_map_left, Category.assoc,
    pullback.lift_fst, Over.mapPullbackAdj_unit_app, Over.homMk_left]
  change pullback.lift (𝟙 U.left) U.hom _ ≫ pullback.fst (U.hom ≫ g) g ≫ p.left = _
  rw [pullback.lift_fst_assoc, Category.id_comp]

/-- Transport the full label homomorphism to the actual base-changed group object. -/
def marking (m : L →* ((Over.map g).obj U ⟶ G)) :
    L →* (U ⟶ (Over.pullback g).obj G) :=
  (pointsMulEquiv g G U).toMonoidHom.comp m

/-- Each transported label retains exactly its original relative scheme map. -/
@[reassoc] theorem marking_fst (m : L →* ((Over.map g).obj U ⟶ G)) (a : L) :
    (marking g G U m a).left ≫ pullback.fst G.hom g = (m a).left :=
  pointsMulEquiv_fst g G U (m a)

/-- Base change preserves and reflects injectivity of every full marking. -/
theorem marking_injective_iff (m : L →* ((Over.map g).obj U ⟶ G)) :
    Function.Injective (marking g G U m) ↔ Function.Injective m :=
  (pointsMulEquiv g G U).injective.of_comp_iff m

end FLT.Mazur.GroupMarkingBaseChange
