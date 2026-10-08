/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafLocalHomComparison

/-!
# Composition of image-open local morphisms

Conjugation from pullback maps to image-open maps preserves composition and
identities. Thus cocycles of pullback maps give cocycles on every image subopen.
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

/-- Extending ordinary restriction maps preserves composition. -/
theorem ofRestriction_comp
    (a : (restrictFunctor i).obj M ⟶ (restrictFunctor i).obj N)
    (b : (restrictFunctor i).obj N ⟶ (restrictFunctor i).obj P) :
    ofRestriction i (a ≫ b) = ofRestriction i a ≫ ofRestriction i b := by
  simp only [ofRestriction, SheafOfModules.Hom.over, Functor.map_comp,
    Category.assoc, IsIso.inv_hom_id_assoc]

/-- Changing from pullback to restriction maps preserves composition. -/
theorem toRestriction_comp
    (a : (pullback i).obj M ⟶ (pullback i).obj N)
    (b : (pullback i).obj N ⟶ (pullback i).obj P) :
    toRestriction i (a ≫ b) = toRestriction i a ≫ toRestriction i b := by
  simp only [toRestriction, Category.assoc, Iso.inv_hom_id_app_assoc]

/-- Extending genuine pullback maps to the image preserves composition. -/
theorem localHom_comp
    (a : (pullback i).obj M ⟶ (pullback i).obj N)
    (b : (pullback i).obj N ⟶ (pullback i).obj P) :
    localHom i (a ≫ b) = localHom i a ≫ localHom i b := by
  rw [localHom, toRestriction_comp, ofRestriction_comp]
  rfl

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
