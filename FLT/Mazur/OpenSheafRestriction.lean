/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Over

/-!
# Restriction to an open and its left adjoint

Restriction evaluates a sheaf on the ambient image of each subspace open.
Its left adjoint is the sheafification of left Kan extension along that image
functor. Before sheafification this extension agrees with the original presheaf
on opens contained in the subspace, and is zero on all other opens.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor TopologicalSpace Opposite

universe u

namespace FLT.Mazur.OpenSheafRestriction

variable {X : TopCat.{u}} (W : Opens X)

/-- The inclusion of an open subspace. -/
def inclusion : TopCat.of W ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The open-image functor of the inclusion. -/
def openImage : Opens W ⥤ Opens X :=
  (W.isOpenEmbedding.isOpenMap : IsOpenMap (inclusion W)).functor

instance inclusion_mono : Mono (inclusion W) :=
  (TopCat.mono_iff_injective _).mpr Subtype.val_injective

instance openImage_full : (openImage W).Full :=
  IsOpenMap.functorFullOfMono
    (f := inclusion W) W.isOpenEmbedding.isOpenMap

instance openImage_faithful : (openImage W).Faithful :=
  inferInstanceAs (IsOpenMap.functor _).Faithful

instance openImage_continuous :
    (openImage W).IsContinuous (Opens.grothendieckTopology W)
      (Opens.grothendieckTopology X) :=
  (W.isOpenEmbedding : Topology.IsOpenEmbedding (inclusion W)).functor_isContinuous

/-- An image open is contained in the chosen ambient open. -/
lemma openImage_le (V : Opens W) : (openImage W).obj V ≤ W := by
  rintro x ⟨y, _, rfl⟩
  exact y.property

/-- Restriction of abelian sheaves to the open subspace. -/
abbrev restriction : TopCat.Sheaf AddCommGrpCat.{u} X ⥤
    TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W) := W.sheafRestrict

/-- Restriction evaluates on the image of a subspace open. -/
lemma restriction_obj_obj (F : TopCat.Sheaf AddCommGrpCat.{u} X) (V : Opens W) :
    ((restriction W).obj F).obj.obj (op V) = F.obj.obj (op ((openImage W).obj V)) := rfl

/-- Global sections of a restriction are sections on the ambient open. -/
def restrictionTopIso (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((restriction W).obj F).obj.obj (op ⊤) ≅ F.obj.obj (op W) :=
  F.obj.mapIso (eqToIso (congrArg op (show (openImage W).obj ⊤ = W by
    ext x
    exact ⟨fun ⟨y, _, h⟩ ↦ h ▸ y.property, fun h ↦ ⟨⟨x, h⟩, trivial, rfl⟩⟩)))

/-- The restriction maps are the original maps on image opens. -/
lemma restriction_obj_map (F : TopCat.Sheaf AddCommGrpCat.{u} X)
    {V T : Opens W} (f : V ⟶ T) :
    ((restriction W).obj F).obj.map f.op = F.obj.map ((openImage W).map f).op := rfl

/-- Coefficient morphisms restrict componentwise. -/
lemma restriction_map_app {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (V : Opens W) :
    ((restriction W).map f).hom.app (op V) = f.hom.app (op ((openImage W).obj V)) := rfl

/-- Extension on presheaves, before sheafification. -/
def extensionPresheaf : (TopCat.of W).Presheaf AddCommGrpCat.{u} ⥤
    X.Presheaf AddCommGrpCat.{u} := (openImage W).op.lan

/-- The presheaf extension is left adjoint to restriction of presheaves. -/
def presheafAdjunction : extensionPresheaf W ⊣
    (whiskeringLeft _ _ AddCommGrpCat.{u}).obj (openImage W).op :=
  (openImage W).op.lanAdjunction _

/-- The unit identifies a presheaf with the restriction of its extension. -/
instance presheafAdjunction_unit_isIso (F : (TopCat.of W).Presheaf AddCommGrpCat.{u}) :
    IsIso ((presheafAdjunction W).unit.app F) :=
  ((openImage W).op.isPointwiseLeftKanExtensionLeftKanExtensionUnit F).isIso_hom

/-- Evaluation of the presheaf extension on an image open. -/
def extensionPresheafImageIso (F : (TopCat.of W).Presheaf AddCommGrpCat.{u})
    (V : Opens W) :
    ((extensionPresheaf W).obj F).obj (op ((openImage W).obj V)) ≅ F.obj (op V) :=
  by
  have := presheafAdjunction_unit_isIso W F
  exact (asIso (((presheafAdjunction W).unit.app F).app (op V))).symm

/-- General evaluation is the colimit over subspace opens containing the given open. -/
def extensionPresheafObjIsoColimit (F : (TopCat.of W).Presheaf AddCommGrpCat.{u})
    (V : Opens X) :
    ((extensionPresheaf W).obj F).obj (op V) ≅
      colimit (CostructuredArrow.proj (openImage W).op (op V) ⋙ F) :=
  (openImage W).op.leftKanExtensionObjIsoColimit F (op V)

/-- No subspace open can contain an ambient open which is not contained in `W`. -/
lemma extensionIndex_isEmpty (V : Opens X) (hV : ¬ V ≤ W) :
    IsEmpty (CostructuredArrow (openImage W).op (op V)) :=
  ⟨fun a ↦ hV (a.hom.unop.le.trans (openImage_le W a.left.unop))⟩

/-- Before sheafification, extension is zero on opens not contained in `W`. -/
lemma extensionPresheaf_obj_isZero (F : (TopCat.of W).Presheaf AddCommGrpCat.{u})
    (V : Opens X) (hV : ¬ V ≤ W) :
    IsZero (((extensionPresheaf W).obj F).obj (op V)) := by
  let := extensionIndex_isEmpty W V hV
  apply IsZero.of_iso _ (extensionPresheafObjIsoColimit W F V)
  rw [IsZero.iff_id_eq_zero]
  apply colimit.hom_ext
  intro a
  exact isEmptyElim a

/-- Extension of abelian sheaves by sheafification of the presheaf extension. -/
def extension : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W) ⥤
    TopCat.Sheaf AddCommGrpCat.{u} X :=
  sheafToPresheaf (Opens.grothendieckTopology W) AddCommGrpCat ⋙
    extensionPresheaf W ⋙ presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat

/-- The actual extension-restriction adjunction. -/
def adjunction : extension W ⊣ restriction W :=
  sheafPullbackConstruction.sheafAdjunctionContinuous (openImage W) AddCommGrpCat
    (Opens.grothendieckTopology W) (Opens.grothendieckTopology X)

instance extension_isLeftAdjoint : (extension W).IsLeftAdjoint :=
  (adjunction W).isLeftAdjoint

instance restriction_isRightAdjoint : (restriction W).IsRightAdjoint :=
  (adjunction W).isRightAdjoint

/-- Extension is computed by sheafifying the displayed presheaf. -/
lemma extension_obj (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W)) :
    (extension W).obj F =
      (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat).obj
        ((extensionPresheaf W).obj F.obj) := rfl

/-- The adjunction identifies maps out of extension with maps into restriction. -/
def homEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W))
    (G : TopCat.Sheaf AddCommGrpCat.{u} X) :
    ((extension W).obj F ⟶ G) ≃ (F ⟶ (restriction W).obj G) :=
  (adjunction W).homEquiv F G

/-- Componentwise evaluation of the adjunction on a subspace open. -/
lemma homEquiv_app (F : TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W))
    (G : TopCat.Sheaf AddCommGrpCat.{u} X) (f : (extension W).obj F ⟶ G)
    (V : Opens W) :
    (homEquiv W F G f).hom.app (op V) =
      ((adjunction W).unit.app F).hom.app (op V) ≫
        f.hom.app (op ((openImage W).obj V)) := by
  rw [homEquiv, Adjunction.homEquiv_unit]
  rfl

end FLT.Mazur.OpenSheafRestriction
