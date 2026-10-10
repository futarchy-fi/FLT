/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineTildeBaseChangeIso

/-!
# Original-section formula for affine base-change isomorphisms

Keep the unit computation abstract in the rings and modules so concrete
geometric scalar structures need not be unfolded by rewriting.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

universe u

namespace FLT.Mazur.AffineTildeBaseChangeIso

variable {R S : CommRingCat.{u}} (φ : R ⟶ S) (M : ModuleCat R) (N : ModuleCat S)

/-- The base-change isomorphism sends each original section to its prescribed coefficient. -/
lemma iso_unit (g : M ⟶ (ModuleCat.restrictScalars φ.hom).obj N)
    (h : let _ := φ.hom.toAlgebra
      let _ := restrictScalarTower φ N
      IsBaseChange S g.hom) (m : M) :
    (iso φ M N g h).hom.app ⊤
      (((pullbackPushforwardAdjunction (Spec.map φ)).unit.app (tilde M)).app ⊤
        (tilde.toOpen M ⊤ m)) = tilde.toOpen N ⊤ (g m) := by
  rw [iso_hom]
  exact AffineTildeSemilinearMap.map_unit φ M N g m

end FLT.Mazur.AffineTildeBaseChangeIso
