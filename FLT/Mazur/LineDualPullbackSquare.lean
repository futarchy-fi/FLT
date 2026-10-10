/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.DualPullbackSquare
public import FLT.Mazur.ModuleSheafDualPullbackRestrict

/-!
# Dual-line transport through the geometric square

For a line bundle the intrinsic dual comparison is invertible. The square
law therefore normalizes transported dual-line maps on the total space.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
open SchemePullbackSquare
variable {P X T S : Scheme.{u}}
  (p : P ⟶ X) (q : P ⟶ T) (f : X ⟶ S) (g : T ⟶ S)
  (w : q ≫ g = p ≫ f) {B : S.Modules} (hB : LocallyFreeRankOne B)

/-- The canonical line-dual isomorphisms satisfy the original square coherence. -/
@[reassoc]
lemma moduleSheafDualPullbackIso_square :
    (pullback q).map (moduleSheafDualPullbackIso g hB).hom ≫
        (moduleSheafDualPullbackIso q (hB.pullback g)).hom ≫
          (moduleSheafDualIso _ ((squareIso f q g p w).app B).symm).hom =
      (squareIso f q g p w).hom.app (moduleSheafDual B) ≫
        (pullback p).map (moduleSheafDualPullbackIso f hB).hom ≫
          (moduleSheafDualPullbackIso p (hB.pullback f)).hom :=
  moduleSheafDualPullbackHom_square p q f g w B

/-- Transporting a dual-line map through the square cancels its inverse pullback comparison. -/
lemma moduleSheafDualPullbackIso_square_map {L : X.Modules}
    (a : moduleSheafDual ((pullback f).obj B) ⟶ L) :
    (pullback q).map (moduleSheafDualPullbackIso g hB).hom ≫
        (moduleSheafDualPullbackIso q (hB.pullback g)).hom ≫
          (moduleSheafDualIso _ ((squareIso f q g p w).app B).symm).hom ≫
            (moduleSheafDualPullbackIso p (hB.pullback f)).inv ≫ (pullback p).map a =
      (squareIso f q g p w).hom.app (moduleSheafDual B) ≫
        (pullback p).map ((moduleSheafDualPullbackIso f hB).hom ≫ a) := by
  have h := congrArg (fun k ↦ k ≫
    (moduleSheafDualPullbackIso p (hB.pullback f)).inv ≫ (pullback p).map a)
    (moduleSheafDualPullbackIso_square p q f g w hB)
  simpa only [Category.assoc, Iso.hom_inv_id_assoc, Functor.map_comp] using h

end FLT.Mazur.FCurve
