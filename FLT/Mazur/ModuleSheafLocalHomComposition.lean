/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalHomComparison
public import FLT.Mazur.ModuleSheafLocalHomNormalization

/-!
# Composition of image-open local morphisms

The imported extension of pullback maps to image opens preserves composition.
Consequently pullback cocycles give cocycles on every image subopen.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.ModuleSheafOpenImmersionLocalHom
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y : Scheme.{u}} (i : Y ⟶ X) [IsOpenImmersion i]
variable {M N P : X.Modules}

/-- A pullback cocycle becomes an equality of maps on every image subopen. -/
theorem localHom_cocycle_app
    (a : (pullback i).obj M ⟶ (pullback i).obj N)
    (b : (pullback i).obj N ⟶ (pullback i).obj P)
    (c : (pullback i).obj M ⟶ (pullback i).obj P) (h : a ≫ b = c)
    (U : X.Opens) (hU : U ≤ i.opensRange) (s : Γ(M, U)) :
    ModuleSheafMorphismGluing.localApp (localHom i b) hU
        (ModuleSheafMorphismGluing.localApp (localHom i a) hU s) =
      ModuleSheafMorphismGluing.localApp (localHom i c) hU s := by
  rw [← h, localHom_comp]
  rfl

end FLT.Mazur.ModuleSheafOpenImmersionLocalHom
