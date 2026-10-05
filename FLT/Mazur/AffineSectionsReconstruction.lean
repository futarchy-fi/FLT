/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Tilde

/-!
# Reconstructing affine quasi-coherent morphisms from sections

The tilde counit lifts linear section maps to actual sheaf morphisms.
The lift is inverse to taking sections, so section isomorphisms lift uniquely.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.AffineSectionsReconstruction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem map_counitLift {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {G : D ⥤ C} (adj : L ⊣ G) {X Y : D}
    [IsIso (adj.counit.app X)] (f : G.obj X ⟶ G.obj Y) :
    G.map (inv (adj.counit.app X) ≫ L.map f ≫ adj.counit.app Y) = f := by
  have hi : G.map (inv (adj.counit.app X)) = adj.unit.app (G.obj X) := by
    apply (cancel_mono (G.map (adj.counit.app X))).mp
    rw [← G.map_comp, IsIso.inv_hom_id, G.map_id, adj.right_triangle_components]
    rfl
  have hn : f ≫ adj.unit.app (G.obj Y) = adj.unit.app (G.obj X) ≫ G.map (L.map f) :=
    adj.unit.naturality f
  rw [G.map_comp, G.map_comp, hi, ← Category.assoc, ← hn,
    Category.assoc, adj.right_triangle_components, Category.comp_id]

variable {A : CommRingCat.{u}} {M N : (Spec A).Modules} [M.IsQuasicoherent]

local instance : IsIso (tilde.adjunction.counit.app M) :=
  inferInstanceAs (IsIso M.fromTildeΓ)

/-- Lift a linear map of global sections to a sheaf morphism. -/
def lift (f : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) : M ⟶ N :=
  inv (tilde.adjunction.counit.app M) ≫ (tilde.functor A).map f ≫
    tilde.adjunction.counit.app N

/-- Taking global sections of the lift recovers the given map. -/
@[simp]
theorem map_lift (f : moduleSpecΓFunctor.obj M ⟶ moduleSpecΓFunctor.obj N) :
    moduleSpecΓFunctor.map (lift f) = f := by
  exact map_counitLift tilde.adjunction f

/-- A sheaf morphism out of a quasi-coherent sheaf is determined by its sections. -/
theorem map_injective : Function.Injective
    (moduleSpecΓFunctor.map : (M ⟶ N) → _) := by
  intro f g h
  apply (cancel_epi M.fromTildeΓ).mp
  have hf := fromTildeΓNatTrans.naturality f
  have hg := fromTildeΓNatTrans.naturality g
  change (tilde.functor A).map (moduleSpecΓFunctor.map f) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ f at hf
  change (tilde.functor A).map (moduleSpecΓFunctor.map g) ≫ N.fromTildeΓ =
    M.fromTildeΓ ≫ g at hg
  rw [← hf, ← hg, h]

/-- Lifting the sections of a sheaf morphism recovers that morphism. -/
@[simp]
theorem lift_map (f : M ⟶ N) : lift (moduleSpecΓFunctor.map f) = f :=
  map_injective (map_lift _)

variable [N.IsQuasicoherent]

/-- Lift a section isomorphism to the unique sheaf isomorphism with those sections. -/
def liftIso (e : moduleSpecΓFunctor.obj M ≅ moduleSpecΓFunctor.obj N) : M ≅ N where
  hom := lift e.hom
  inv := lift e.inv
  hom_inv_id := map_injective (by simp)
  inv_hom_id := map_injective (by simp)

/-- The lifted isomorphism has exactly the prescribed global section isomorphism. -/
@[simp]
theorem mapIso_liftIso (e : moduleSpecΓFunctor.obj M ≅ moduleSpecΓFunctor.obj N) :
    moduleSpecΓFunctor.mapIso (liftIso e) = e := by
  apply Iso.ext
  exact map_lift e.hom

/-- The reconstruction also preserves an existing sheaf isomorphism exactly. -/
@[simp]
theorem liftIso_mapIso (e : M ≅ N) : liftIso (moduleSpecΓFunctor.mapIso e) = e := by
  apply Iso.ext
  exact lift_map e.hom

end FLT.Mazur.AffineSectionsReconstruction
