/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenSheafRestriction
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Topology.Sheaves.Sheafify

/-!
# Stalks of extension from an open subspace

The left adjoint constructed in `OpenSheafRestriction` has the original stalk
at each point of the open, and zero stalk at every point outside it. The latter
includes boundary points: every neighborhood of such a point has zero value in
the presheaf extension, and sheafification leaves stalks unchanged.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite
open TopCat.Presheaf
open scoped ZeroObject

universe u

namespace FLT.Mazur.OpenSheafRestriction

variable {X : TopCat.{u}} (W : Opens X)

/-- Restricting a presheaf to an open subspace preserves its stalk at each point there. -/
def restrictionPresheafStalkIso (P : X.Presheaf AddCommGrpCat.{u}) (x : W) :
    stalk P x.val ≅ stalk (X := TopCat.of W) ((openImage W).op ⋙ P) x :=
  stalkPullbackIso AddCommGrpCat.{u} (inclusion W) P x ≪≫
    (stalkFunctor (X := TopCat.of W) AddCommGrpCat.{u} x).mapIso
      ((IsOpenMap.pullbackIso (C := AddCommGrpCat.{u})
        (W.isOpenEmbedding.isOpenMap : IsOpenMap (inclusion W))).app P)

/-- At a point of the open, the presheaf extension has the original stalk. -/
def extensionPresheafStalkIso (F : (TopCat.of W).Presheaf AddCommGrpCat.{u}) (x : W) :
    stalk ((extensionPresheaf W).obj F) x.val ≅ stalk F x :=
  restrictionPresheafStalkIso W ((extensionPresheaf W).obj F) x ≪≫
    (stalkFunctor (X := TopCat.of W) AddCommGrpCat.{u} x).mapIso
      (asIso ((presheafAdjunction W).unit.app F)).symm

/-- Outside the open every neighborhood contributes a zero group to the stalk. -/
lemma extensionPresheafStalk_isZero (F : (TopCat.of W).Presheaf AddCommGrpCat.{u})
    (x : X) (hx : x ∉ W) : IsZero (stalk ((extensionPresheaf W).obj F) x) := by
  rw [IsZero.iff_id_eq_zero]
  apply stalk_hom_ext
  intro V hxV
  exact (extensionPresheaf_obj_isZero W F V (fun h ↦ hx (h hxV))).eq_of_src _ _

/-- Sheafification supplies the canonical comparison on extension stalks. -/
def extensionSheafifyStalkIso (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W)) (x : X) :
    stalk ((extensionPresheaf W).obj F.obj) x ≅ stalk ((extension W).obj F).obj x := by
  letI := stalkFunctor_map_unit_toSheafify_isIso x AddCommGrpCat.{u}
    ((extensionPresheaf W).obj F.obj)
  exact asIso ((stalkFunctor AddCommGrpCat.{u} x).map
    (toSheafify (Opens.grothendieckTopology X) ((extensionPresheaf W).obj F.obj)))

/-- The left adjoint's stalk inside the open is the original sheaf's stalk. -/
def extensionStalkIso (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W)) (x : W) :
    stalk ((extension W).obj F).obj x.val ≅ stalk F.obj x :=
  (extensionSheafifyStalkIso W F x.val).symm ≪≫ extensionPresheafStalkIso W F.obj x

/-- Membership in the open gives the same stalk comparison with an ambient point. -/
def extensionStalkIsoOfMem (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W))
    (x : X) (hx : x ∈ W) :
    stalk ((extension W).obj F).obj x ≅ stalk F.obj (⟨x, hx⟩ : W) :=
  extensionStalkIso W F ⟨x, hx⟩

/-- The left adjoint's stalk is zero at every point outside the open. -/
lemma extensionStalk_isZero (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W))
    (x : X) (hx : x ∉ W) : IsZero (stalk ((extension W).obj F).obj x) :=
  (extensionPresheafStalk_isZero W F.obj x hx).of_iso
    (extensionSheafifyStalkIso W F x).symm

/-- The outside stalk is canonically isomorphic to the zero abelian group. -/
def extensionStalkZeroIso (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W))
    (x : X) (hx : x ∉ W) : stalk ((extension W).obj F).obj x ≅ (0 : AddCommGrpCat.{u}) :=
  (extensionStalk_isZero W F x hx).isoZero

/-- Every element of an outside stalk is zero. -/
lemma extensionStalk_eq_zero (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W))
    (x : X) (hx : x ∉ W) (s : (stalk ((extension W).obj F).obj x : AddCommGrpCat.{u})) : s = 0 := by
  have := AddCommGrpCat.subsingleton_of_isZero (extensionStalk_isZero W F x hx)
  exact Subsingleton.elim _ _

/-- The sheafification comparison commutes with coefficient morphisms. -/
@[reassoc]
lemma extensionSheafifyStalkIso_naturality
    {F G : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W)} (f : F ⟶ G) (x : X) :
    (stalkFunctor AddCommGrpCat.{u} x).map ((extensionPresheaf W).map f.hom) ≫
        (extensionSheafifyStalkIso W G x).hom =
      (extensionSheafifyStalkIso W F x).hom ≫
        (stalkFunctor AddCommGrpCat.{u} x).map ((extension W).map f).hom := by
  change (stalkFunctor AddCommGrpCat.{u} x).map _ ≫
      (stalkFunctor AddCommGrpCat.{u} x).map _ =
    (stalkFunctor AddCommGrpCat.{u} x).map _ ≫ (stalkFunctor AddCommGrpCat.{u} x).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact congrArg _ (toSheafify_naturality (Opens.grothendieckTopology X) _)

end FLT.Mazur.OpenSheafRestriction
