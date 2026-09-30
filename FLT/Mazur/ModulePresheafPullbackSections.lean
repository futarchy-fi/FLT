/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.CategoryTheory.Filtered.Basic

/-!
# Sections of presheaf pullback

For an open `V`, the chosen module-presheaf pullback is the filtered colimit
of scalar-extended sections over opens `U` with `V ≤ f ⁻¹ᵁ U`. The comparison
uses the pullback adjunction and a right adjoint to evaluation at `V`.
Finite intersections of opens give filteredness of the indexing category.
-/

open CategoryTheory AlgebraicGeometry Opposite Limits
open scoped ChangeOfRings
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

@[expose] public noncomputable section

namespace FLT.Mazur.FCurve.ModulePresheafPullbackSections
variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens)
/-- Opens whose inverse image contains the fixed source open. -/
abbrev Index := { U : Y.Opens // V ≤ f ⁻¹ᵁ U }
instance : Nonempty (Index f V) := ⟨⟨⊤, by simp⟩⟩
instance : IsCofiltered (Index f V) where
  cone_objs U W := ⟨⟨U.val ⊓ W.val, by
      change V ≤ (f ⁻¹ᵁ U.val) ⊓ (f ⁻¹ᵁ W.val)
      exact le_inf U.property W.property⟩,
    homOfLE (show U.val ⊓ W.val ≤ U.val from inf_le_left),
    homOfLE (show U.val ⊓ W.val ≤ W.val from inf_le_right), trivial⟩
  cone_maps _ _ _ _ := ⟨_, 𝟙 _, Subsingleton.elim _ _⟩

/-- The scalar map from a target open to the fixed source open. -/
abbrev scalar (U : Index f V) := (f.appLE U.val V U.property).hom
/-- The scalar-extended module of sections for one indexing open. -/
abbrev term (M : Y.PresheafOfModules) (U : Index f V) : ModuleCat Γ(X, V) :=
  (ModuleCat.extendScalars (scalar f V U)).obj (M.obj (op U.val))

/-- Scalar maps commute with restriction of the indexing open. -/
lemma scalar_comp {U W : Index f V} (i : W ⟶ U) :
    (scalar f V W).comp (Y.presheaf.map
      (homOfLE (show W.val ≤ U.val from i.le)).op).hom = scalar f V U :=
  congrArg CommRingCat.Hom.hom (f.map_appLE W.property (homOfLE (show W.val ≤ U.val from i.le)).op)

/-- The scalar-extension unit on a module of sections. -/
abbrev insert (M : Y.PresheafOfModules) (U : Index f V) :
    M.obj (op U.val) ⟶ (ModuleCat.restrictScalars (scalar f V U)).obj (term f V M U) :=
  (ModuleCat.extendRestrictScalarsAdj (scalar f V U)).unit.app _

/-- Restriction induces a linear map between the scalar-extended terms. -/
noncomputable def transition (M : Y.PresheafOfModules) {U W : Index f V} (i : W ⟶ U) :
    term f V M U ⟶ term f V M W :=
  ((ModuleCat.extendRestrictScalarsAdj (scalar f V U)).homEquiv _ _).symm
    (M.map (homOfLE (show W.val ≤ U.val from i.le)).op ≫
      (ModuleCat.restrictScalars _).map (insert f V M W) ≫
      (ModuleCat.restrictScalarsComp' _ _ _ (scalar_comp f V i).symm).inv.app _)

/-- The transition map restricts the section in a generating tensor. -/
lemma transition_one (M : Y.PresheafOfModules) {U W : Index f V} (i : W ⟶ U)
    (m : M.obj (op U.val)) :
    transition f V M i ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U.val), scalar f V U] m) =
      (1 : Γ(X, V)) ⊗ₜ[Γ(Y, W.val), scalar f V W] (show M.obj (op W.val) from
        M.map (homOfLE (show W.val ≤ U.val from i.le)).op m) := by
  have h := congrArg (fun g => g m)
    (((ModuleCat.extendRestrictScalarsAdj (scalar f V U)).homEquiv _ _).apply_symm_apply
      (M.map (homOfLE (show W.val ≤ U.val from i.le)).op ≫
        (ModuleCat.restrictScalars _).map (insert f V M W) ≫
        (ModuleCat.restrictScalarsComp' _ _ _ (scalar_comp f V i).symm).inv.app _))
  exact h

/-- The filtered diagram of scalar-extended sections. -/
noncomputable def diagram (M : Y.PresheafOfModules) :
    (Index f V)ᵒᵖ ⥤ ModuleCat Γ(X, V) where
  obj U := term f V M U.unop
  map i := transition f V M i.unop
  map_id U := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    rw [transition_one]
    change ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U.unop.val), scalar f V U.unop]
      (show M.obj (op U.unop.val) from M.map (𝟙 _) m)) = _
    simp only [PresheafOfModules.map_id]
    rfl
  map_comp i j := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    simp only [ModuleCat.comp_apply, transition_one]
    erw [transition_one]
    congr 1
    exact M.map_comp_apply _ _ m

section Cofree
variable (A : ModuleCat.{u} Γ(X, V))
/-- Sections of the right adjoint to evaluation at an open. -/
def cofreeObj (W : X.Opens) : ModuleCat.{u} Γ(X, W) :=
  ModuleCat.of _ (∀ h : PLift (V ≤ W),
    (ModuleCat.restrictScalars (X.presheaf.map (homOfLE h.down).op).hom).obj A)
/-- The module presheaf right adjoint to evaluation at the fixed open. -/
def cofree : X.PresheafOfModules where
  obj W := cofreeObj V A W.unop
  map {W W'} i := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (X.ringCatSheaf.obj.map i).hom).obj
      (cofreeObj V A W'.unop))
    { toFun := fun s h => s ⟨h.down.trans i.unop.le⟩
      map_add' := by intros; rfl
      map_smul' := by
        intro r s
        funext h
        change (X.presheaf.map (homOfLE (h.down.trans i.unop.le)).op) r • s _ =
          X.presheaf.map (homOfLE h.down).op (X.presheaf.map i r) • s _
        rw [← CommRingCat.comp_apply, ← X.presheaf.map_comp]
        rfl }
  map_id W := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    funext h
    rfl
  map_comp i j := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    funext h
    rfl

/-- Extend a linear map on one open to the right-adjoint presheaf. -/
def cofreeLift (N : X.PresheafOfModules) (g : N.obj (op V) ⟶ A) : N ⟶ cofree V A where
  app W := ModuleCat.ofHom
    { toFun := fun s h => g (N.map (homOfLE h.down).op s)
      map_add' := by
        intro s t
        funext h
        exact (congrArg g ((N.map _).hom.map_add s t)).trans (g.hom.map_add _ _)
      map_smul' := by
        intro r s
        ext h
        change g (N.map (homOfLE h.down).op (r • s)) =
          (X.presheaf.map (homOfLE h.down).op) r • g (N.map (homOfLE h.down).op s)
        rw [N.map_smul, map_smul]
        rfl }
  naturality i := by
    ext s
    funext h
    change g (N.map (homOfLE h.down).op (N.map i s)) = _
    rw [← N.map_comp_apply]
    rfl

/-- Evaluate a map into the right-adjoint presheaf at its distinguished open. -/
def cofreeEval (N : X.PresheafOfModules) (g : N ⟶ cofree V A) : N.obj (op V) ⟶ A :=
  ModuleCat.ofHom
    { toFun := fun s => g.app (op V) s ⟨le_rfl⟩
      map_add' := by
        intro s t
        exact congrFun ((g.app (op V)).hom.map_add s t) ⟨le_rfl⟩
      map_smul' := by
        intro r s
        have h := congrFun ((g.app (op V)).hom.map_smul r s) ⟨le_rfl⟩
        change g.app (op V) (r • s) ⟨le_rfl⟩ =
          X.presheaf.map (𝟙 (op V)) r • (show A from g.app (op V) s ⟨le_rfl⟩) at h
        simpa using h }

/-- Evaluation recovers the original linear map. -/
lemma cofreeEval_lift (N : X.PresheafOfModules) (g : N.obj (op V) ⟶ A) :
    cofreeEval V A N (cofreeLift V A N g) = g := by
  ext s
  change g (N.map (𝟙 _) s) = g s
  rw [N.map_id]
  rfl
/-- Every map into the right-adjoint presheaf comes from evaluation. -/
lemma cofreeLift_eval (N : X.PresheafOfModules) (g : N ⟶ cofree V A) :
    cofreeLift V A N (cofreeEval V A N g) = g := by
  ext W s
  funext h
  exact congrFun (PresheafOfModules.naturality_apply g (homOfLE h.down).op s) ⟨le_rfl⟩

end Cofree
/-- The existing presheaf pullback, without sheafification. -/
abbrev pull (M : Y.PresheafOfModules) :=
  (PresheafOfModules.pullback f.toRingCatSheafHom.hom).obj M
/-- The existing presheaf pullback/pushforward adjunction. -/
abbrev adj := PresheafOfModules.pullbackPushforwardAdjunction f.toRingCatSheafHom.hom

/-- Restrict the image of a section under a map into a pushforward. -/
def sectionMap {M : Y.PresheafOfModules} {N : X.PresheafOfModules}
    (ψ : M ⟶ (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj N)
    (U : Index f V) : M.obj (op U.val) ⟶
      (ModuleCat.restrictScalars (scalar f V U)).obj (N.obj (op V)) :=
  ModuleCat.ofHom (Y := (ModuleCat.restrictScalars (scalar f V U)).obj (N.obj (op V)))
    { toFun := fun m => N.map (homOfLE U.property).op (ψ.app (op U.val) m)
      map_add' := by
        intro m n
        exact (congrArg (N.map _) ((ψ.app _).hom.map_add m n)).trans
          ((N.map _).hom.map_add _ _)
      map_smul' := by
        intro r m
        rw [(ψ.app (op U.val)).hom.map_smul]
        change N.map (homOfLE U.property).op (f.app U.val r •
          (show N.obj (op (f ⁻¹ᵁ U.val)) from ψ.app (op U.val) m)) = _
        rw [N.map_smul]
        rfl }

/-- The canonical map from a scalar-extended term into pullback sections. -/
def component (M : Y.PresheafOfModules) (U : Index f V) :
    term f V M U ⟶ (pull f M).obj (op V) :=
  ((ModuleCat.extendRestrictScalarsAdj (scalar f V U)).homEquiv _ _).symm
    (sectionMap f V ((adj f).unit.app M) U)

/-- The comparison sends a generating tensor to the restricted adjunction unit. -/
lemma component_one (M : Y.PresheafOfModules) (U : Index f V)
    (m : M.obj (op U.val)) :
    component f V M U ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U.val), scalar f V U] m) =
      (pull f M).map (homOfLE U.property).op (((adj f).unit.app M).app (op U.val) m) :=
  congrArg (fun g => g m)
    (((ModuleCat.extendRestrictScalarsAdj (scalar f V U)).homEquiv _ _).apply_symm_apply
      (sectionMap f V ((adj f).unit.app M) U))

set_option maxHeartbeats 600000 in
-- Naturality unfolds both scalar restriction and the chosen pullback adjunction.
/-- The pullback sections with their canonical scalar-extension maps. -/
def cocone (M : Y.PresheafOfModules) : Cocone (diagram f V M) where
  pt := (pull f M).obj (op V)
  ι.app U := component f V M U.unop
  ι.naturality {U W} i := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    simp only [Functor.const_obj_map, ModuleCat.comp_apply]
    change component f V M W.unop (transition f V M i.unop _) = _
    rw [transition_one, component_one]
    erw [component_one]
    erw [PresheafOfModules.naturality_apply]
    exact ((pull f M).map_comp_apply _ _ _).symm

/-- A cocone gives a morphism into the pushforward of the evaluation right adjoint. -/
def coconeMorphism {M : Y.PresheafOfModules} (c : Cocone (diagram f V M)) :
    M ⟶ (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj (cofree V c.pt) where
  app U := ModuleCat.ofHom
    (Y := ((PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj (cofree V c.pt)).obj U)
    { toFun := fun m h => c.ι.app (op ⟨U.unop, h.down⟩)
        ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U.unop), scalar f V ⟨U.unop, h.down⟩] m)
      map_add' := by
        intro m n
        funext h
        exact (congrArg (c.ι.app _) (TensorProduct.tmul_add _ _ _)).trans
          ((c.ι.app _).hom.map_add _ _)
      map_smul' := by
        intro r m
        funext h
        exact ((insert f V M ⟨U.unop, h.down⟩) ≫
          (ModuleCat.restrictScalars _).map (c.ι.app (op ⟨U.unop, h.down⟩))).hom.map_smul r m }
  naturality {U W} i := by
    ext m
    funext h
    have e := ConcreteCategory.congr_hom
      (c.w (homOfLE (show (⟨W.unop, h.down⟩ : Index f V) ≤
        ⟨U.unop, h.down.trans ((TopologicalSpace.Opens.map f.base).map i.unop).le⟩
        from i.unop.le)).op)
      ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U.unop), scalar f V
        ⟨U.unop, h.down.trans ((TopologicalSpace.Opens.map f.base).map i.unop).le⟩] m)
    dsimp only [ModuleCat.comp_apply, diagram] at e
    erw [ModuleCat.comp_apply, transition_one] at e
    exact e

/-- Transpose a linear map from pullback sections using the two adjunctions. -/
def transpose {M : Y.PresheafOfModules} {A : ModuleCat.{u} Γ(X, V)}
    (g : (pull f M).obj (op V) ⟶ A) :
    M ⟶ (PresheafOfModules.pushforward f.toRingCatSheafHom.hom).obj (cofree V A) :=
  (adj f).homEquiv _ _ (cofreeLift V A (pull f M) g)

/-- Transposition evaluates on the canonical section generators. -/
lemma transpose_apply {M : Y.PresheafOfModules} {A : ModuleCat.{u} Γ(X, V)}
    (g : (pull f M).obj (op V) ⟶ A) (U : Index f V) (m : M.obj (op U.val)) :
    (transpose f V g).app (op U.val) m ⟨U.property⟩ =
      g (component f V M U ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U.val), scalar f V U] m)) := by
  rw [component_one]
  rfl

/-- The universal map from pullback sections to a cocone vertex. -/
def desc {M : Y.PresheafOfModules} (c : Cocone (diagram f V M)) :
    (pull f M).obj (op V) ⟶ c.pt :=
  cofreeEval V c.pt (pull f M) (((adj f).homEquiv _ _).symm (coconeMorphism f V c))

/-- The universal map transposes to the morphism defined by the cocone. -/
lemma transpose_desc {M : Y.PresheafOfModules} (c : Cocone (diagram f V M)) :
    transpose f V (desc f V c) = coconeMorphism f V c := by
  unfold transpose desc
  rw [cofreeLift_eval, Equiv.apply_symm_apply]

/-- Maps on pullback sections are determined by their transposes. -/
lemma transpose_injective {M : Y.PresheafOfModules} {A : ModuleCat.{u} Γ(X, V)} :
    Function.Injective (transpose f V (M := M) (A := A)) := by
  intro g h e
  have e' := ((adj f).homEquiv _ _).injective e
  have e'' := congrArg (cofreeEval V A (pull f M)) e'
  simpa only [cofreeEval_lift] using e''

/-- The canonical cocone on the scalar-extended section diagram is colimiting. -/
def isColimit (M : Y.PresheafOfModules) : IsColimit (cocone f V M) where
  desc := desc f V
  fac c U := by
    apply ModuleCat.ExtendScalars.hom_ext
    intro m
    exact (transpose_apply f V (desc f V c) U.unop m).symm.trans
      (congrArg (fun g => g.app (op U.unop.val) m ⟨U.unop.property⟩) (transpose_desc f V c))
  uniq c g hg := by
    apply transpose_injective f V
    rw [transpose_desc]
    ext U m
    funext h
    rw [transpose_apply f V g ⟨U.unop, h.down⟩ m]
    exact ConcreteCategory.congr_hom (hg (op ⟨U.unop, h.down⟩)) _

/-- The filtered section colimit identifies with the chosen presheaf pullback. -/
def sectionsIso (M : Y.PresheafOfModules) :
    colimit (diagram f V M) ≅ (pull f M).obj (op V) :=
  (colimit.isColimit _).coconePointUniqueUpToIso (isColimit f V M)

/-- The colimit comparison intertwines its structure maps with the canonical maps. -/
@[reassoc]
lemma ι_sectionsIso_hom (M : Y.PresheafOfModules) (U : Index f V) :
    colimit.ι (diagram f V M) (op U) ≫ (sectionsIso f V M).hom = component f V M U :=
  (colimit.isColimit _).comp_coconePointUniqueUpToIso_hom (isColimit f V M) (op U)

/-- The section comparison on an arbitrary scalar-extended pure tensor. -/
lemma component_tmul (M : Y.PresheafOfModules) (U : Index f V)
    (r : Γ(X, V)) (m : M.obj (op U.val)) :
    component f V M U (r ⊗ₜ[Γ(Y, U.val), scalar f V U] m) =
      r • (pull f M).map (homOfLE U.property).op
        (((adj f).unit.app M).app (op U.val) m) := by
  have h : (r ⊗ₜ[Γ(Y, U.val), scalar f V U] m : term f V M U) =
      r • ((1 : Γ(X, V)) ⊗ₜ[Γ(Y, U.val), scalar f V U] m) := by
    rw [ModuleCat.ExtendScalars.smul_tmul, mul_one]
  rw [h, map_smul, component_one]

/-- The colimit isomorphism on a scalar-extended pure tensor. -/
lemma sectionsIso_tmul (M : Y.PresheafOfModules) (U : Index f V)
    (r : Γ(X, V)) (m : M.obj (op U.val)) :
    (sectionsIso f V M).hom (colimit.ι (diagram f V M) (op U)
      (r ⊗ₜ[Γ(Y, U.val), scalar f V U] m)) =
      r • (pull f M).map (homOfLE U.property).op
        (((adj f).unit.app M).app (op U.val) m) := by
  rw [← ModuleCat.comp_apply, ι_sectionsIso_hom]
  exact component_tmul f V M U r m

/-- The section generators commute with restriction in the source open. -/
lemma component_restrict (M : Y.PresheafOfModules) {W : X.Opens} (i : W ⟶ V)
    (U : Index f V) (r : Γ(X, V)) (m : M.obj (op U.val)) :
    (pull f M).map i.op (component f V M U (r ⊗ₜ[Γ(Y, U.val), scalar f V U] m)) =
      component f W M ⟨U.val, i.le.trans U.property⟩
        (X.presheaf.map i.op r ⊗ₜ[Γ(Y, U.val), scalar f W ⟨U.val, i.le.trans U.property⟩] m) := by
  rw [component_tmul, component_tmul, PresheafOfModules.map_smul,
    ← PresheafOfModules.map_comp_apply]
  rfl

/-- The section generators are natural in the module presheaf. -/
lemma component_map {M N : Y.PresheafOfModules} (α : M ⟶ N)
    (U : Index f V) (r : Γ(X, V)) (m : M.obj (op U.val)) :
    ((PresheafOfModules.pullback f.toRingCatSheafHom.hom).map α).app (op V)
      (component f V M U (r ⊗ₜ[Γ(Y, U.val), scalar f V U] m)) =
      component f V N U (r ⊗ₜ[Γ(Y, U.val), scalar f V U] (α.app (op U.val) m)) := by
  rw [component_tmul, component_tmul, map_smul, PresheafOfModules.naturality_apply]
  congr 2
  exact ConcreteCategory.congr_hom
    (congrArg (fun g => g.app (op U.val)) ((adj f).unit.naturality α)) m |>.symm

end FLT.Mazur.FCurve.ModulePresheafPullbackSections
