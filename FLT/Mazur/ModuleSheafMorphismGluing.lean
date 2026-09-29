/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Gluing morphisms of module sheaves

Compatible linear maps on an open cover glue by the additive sheaf condition.
Their glued section maps are linear because equality can be checked locally.
Restrictions are expressed on slice sites, so overlap equalities refer to every
subopen of the intersection.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace FLT.Mazur.ModuleSheafMorphismGluing

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Restrict a section along an inclusion of opens. -/
abbrev res (M : X.Modules) {U V : X.Opens} (h : U ≤ V) : Γ(M, V) →+ Γ(M, U) :=
  (M.presheaf.map (homOfLE h).op).hom

@[simp]
lemma res_res (M : X.Modules) {U V W : X.Opens} (h : U ≤ V) (k : V ≤ W)
    (s : Γ(M, W)) : res M h (res M k s) = res M (h.trans k) s := by
  exact (congr($(M.presheaf.map_comp (homOfLE k).op (homOfLE h).op) s)).symm

@[simp]
lemma res_self (M : X.Modules) (U : X.Opens) (s : Γ(M, U)) : res M le_rfl s = s := by
  exact congr($(M.presheaf.map_id (op U)) s)

/-- Evaluate a local module morphism on a subopen. -/
abbrev localApp {U V : X.Opens} (φ : M.over U ⟶ N.over U) (h : V ≤ U) :
    Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V) :=
  (φ.val.app (op (Over.mk (homOfLE h)))).hom

lemma localApp_res {U V W : X.Opens} (φ : M.over U ⟶ N.over U)
    (h : V ≤ W) (k : W ≤ U) (s : Γ(M, W)) :
    localApp φ (h.trans k) (res M h s) = res N h (localApp φ k s) := by
  exact congr($((PresheafOfModules.toPresheaf _).map φ.val |>.naturality
    (Over.homMk (homOfLE h) : Over.mk (homOfLE (h.trans k)) ⟶
      Over.mk (homOfLE k)).op) s)

/-- Reindex additive maps from the slice site to the open subscheme. -/
def additiveRestrictionEquiv (U : X.Opens) :
    ((M.over U).val.presheaf ⟶ (N.over U).val.presheaf) ≃
      ((M.restrict U.ι).presheaf ⟶ (N.restrict U.ι).presheaf) :=
  (Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ Ab).obj U.overEquivalence.inverse.op)).homEquiv

/-- On an open subscheme the scalar action is the original action on image opens. -/
lemma restrict_smul (M : X.Modules) (U : X.Opens) (W : U.toScheme.Opens)
    (r : Γ(U.toScheme, W)) :
    (M.restrict U.ι).smul r = M.smul (U := U.ι ''ᵁ W) r := by
  change M.smul ((U.ι.appIso W).inv r) = _
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- Reindexing preserves and reflects linearity. -/
lemma additiveRestrictionEquiv_linear (U : X.Opens)
    (a : (M.over U).val.presheaf ⟶ (N.over U).val.presheaf) :
    (∀ (V : Over U) (r : Γ(X, V.left)) (s : Γ(M, V.left)),
      a.app (op V) (r • s) = (N.smul r).hom (a.app (op V) s)) ↔
    (∀ (W : U.toScheme.Opensᵒᵖ) (r : Γ(U.toScheme, W.unop))
      (s : Γ(M.restrict U.ι, W.unop)),
      (additiveRestrictionEquiv U a).app W (r • s) =
        ((N.restrict U.ι).smul r).hom ((additiveRestrictionEquiv U a).app W s)) := by
  constructor
  · intro h W r s
    change a.app (op (U.overEquivalence.inverse.obj W.unop))
      (((M.restrict U.ι).smul r).hom s) =
        (((N.restrict U.ι).smul r).hom _)
    rw [restrict_smul, restrict_smul]
    exact h (U.overEquivalence.inverse.obj W.unop) r s
  · intro h V
    have he : U.overEquivalence.inverse.obj (U.overEquivalence.functor.obj V) =
        V := by
      refine CostructuredArrow.obj_ext _ _ ?_ (Subsingleton.elim _ _)
      exact (leOfHom (U.overEquivalence.unitIso.inv.app V).left).antisymm
        (leOfHom (U.overEquivalence.unitIso.hom.app V).left)
    rw [← he]
    intro r s
    have hh := h (op (U.overEquivalence.functor.obj V)) r s
    change a.app (op (U.overEquivalence.inverse.obj
      (U.overEquivalence.functor.obj V))) (((M.restrict U.ι).smul r).hom s) =
      (((N.restrict U.ι).smul r).hom _) at hh
    rw [restrict_smul, restrict_smul] at hh
    exact hh

/-- Actual module morphisms on an open subscheme and on its slice site are equivalent. -/
def restrictionEquiv (U : X.Opens) :
    (M.over U ⟶ N.over U) ≃ (M.restrict U.ι ⟶ N.restrict U.ι) where
  toFun a := ⟨PresheafOfModules.homMk
    (additiveRestrictionEquiv U ((PresheafOfModules.toPresheaf _).map a.val))
    ((additiveRestrictionEquiv_linear U _).mp (fun V r s ↦
      (a.val.app (op V)).hom.map_smul r s))⟩
  invFun a := ⟨PresheafOfModules.homMk
    ((additiveRestrictionEquiv U).symm a.mapPresheaf) (by
      have h := (additiveRestrictionEquiv_linear (M := M) (N := N) U
        ((additiveRestrictionEquiv U).symm a.mapPresheaf)).mpr (by
          rw [Equiv.apply_symm_apply]
          exact fun W r s ↦ a.app_smul r s)
      exact fun V r s ↦ h V.unop r s)⟩
  left_inv a := by
    apply SheafOfModules.hom_ext
    apply (PresheafOfModules.toPresheaf _).map_injective
    change (PresheafOfModules.toPresheaf _).map
      (PresheafOfModules.homMk _ _) = _
    have he : Scheme.Modules.Hom.mapPresheaf (⟨PresheafOfModules.homMk
        (additiveRestrictionEquiv U ((PresheafOfModules.toPresheaf _).map a.val))
        ((additiveRestrictionEquiv_linear U _).mp (fun V r s ↦
          (a.val.app (op V)).hom.map_smul r s))⟩ :
        M.restrict U.ι ⟶ N.restrict U.ι) =
        additiveRestrictionEquiv U ((PresheafOfModules.toPresheaf _).map a.val) := by
      ext V s
      rfl
    have hh := (congrArg (additiveRestrictionEquiv U).symm he).trans
      ((additiveRestrictionEquiv U).symm_apply_apply _)
    ext V s
    exact congrArg (fun c ↦ c.app V s) hh
  right_inv a := by
    apply (Scheme.Modules.toPresheaf _).map_injective
    exact (additiveRestrictionEquiv U).apply_symm_apply _

@[simp]
lemma restrictionEquiv_over (U : X.Opens) (a : M ⟶ N) :
    restrictionEquiv U (a.over U) = (restrictFunctor U.ι).map a := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

variable {ι : Type v} (U : ι → X.Opens) (hU : iSup U = ⊤)

include hU

/-- The cover induces a cover on each open. -/
lemma cover_inf (V : X.Opens) : V ≤ ⨆ i, V ⊓ U i := by
  rw [← inf_iSup_eq, hU, inf_top_eq]

/-- Equality of sections can be tested on any open cover. -/
lemma section_ext (V : X.Opens) (s t : Γ(N, V))
    (h : ∀ i, res N (inf_le_left : V ⊓ U i ≤ V) s = res N inf_le_left t) : s = t :=
  TopCat.Sheaf.eq_of_locally_eq'
    (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i ↦ V ⊓ U i) V (fun _ ↦ homOfLE inf_le_left) (cover_inf U hU V) s t h

/-- Genuine equality of the two local morphisms on all subopens of an overlap. -/
def Compatible (φ : ∀ i, M.over (U i) ⟶ N.over (U i)) : Prop :=
  ∀ (i j) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j),
    localApp (φ i) hi = localApp (φ j) hj

variable (φ : ∀ i, M.over (U i) ⟶ N.over (U i)) (hφ : Compatible U φ)

include hφ in
/-- The images of a section under compatible local maps glue uniquely. -/
lemma existsUnique_section (V : X.Opens) (s : Γ(M, V)) :
    ∃! t : Γ(N, V), ∀ i, res N (inf_le_left : V ⊓ U i ≤ V) t =
      localApp (φ i) inf_le_right (res M inf_le_left s) := by
  apply TopCat.Sheaf.existsUnique_gluing'
    (⟨N.presheaf, N.isSheaf⟩ : TopCat.Sheaf Ab X)
    (fun i ↦ V ⊓ U i) V (fun _ ↦ homOfLE inf_le_left) (cover_inf U hU V)
  intro i j
  change res N inf_le_left (localApp (φ i) inf_le_right (res M inf_le_left s)) =
    res N inf_le_right (localApp (φ j) inf_le_right (res M inf_le_left s))
  rw [← localApp_res, ← localApp_res, res_res, res_res]
  rw [hφ i j _ _ _]

/-- The glued image of a section. -/
def glueSection (V : X.Opens) (s : Γ(M, V)) : Γ(N, V) :=
  (existsUnique_section U hU φ hφ V s).exists.choose

lemma res_glueSection (V : X.Opens) (s : Γ(M, V)) (i : ι) :
    res N (inf_le_left : V ⊓ U i ≤ V) (glueSection U hU φ hφ V s) =
      localApp (φ i) inf_le_right (res M inf_le_left s) :=
  (existsUnique_section U hU φ hφ V s).exists.choose_spec i

/-- On a subopen of one chart the glued section has the prescribed value. -/
lemma glueSection_of_le (V : X.Opens) (i : ι) (h : V ≤ U i) (s : Γ(M, V)) :
    glueSection U hU φ hφ V s = localApp (φ i) h s := by
  apply section_ext U hU V
  intro j
  rw [res_glueSection, ← localApp_res, hφ j i _ _ _]

lemma glueSection_res {V W : X.Opens} (h : V ≤ W) (s : Γ(M, W)) :
    glueSection U hU φ hφ V (res M h s) =
      res N h (glueSection U hU φ hφ W s) := by
  apply section_ext U hU V
  intro i
  let k : V ⊓ U i ≤ W ⊓ U i := inf_le_inf_right _ h
  have ht := congrArg (res N k) (res_glueSection U hU φ hφ W s i)
  rw [res_res, ← localApp_res, res_res] at ht
  rw [res_glueSection, res_res, res_res]
  exact ht.symm

/-- Additive sections glue to a natural transformation. -/
def glueAdditive : M.presheaf ⟶ N.presheaf where
  app V := AddCommGrpCat.ofHom
    { toFun := glueSection U hU φ hφ V.unop
      map_zero' := by
        apply section_ext U hU V.unop
        intro i
        change res N inf_le_left (glueSection U hU φ hφ V.unop 0) =
          res N inf_le_left 0
        simp only [res_glueSection, map_zero]
      map_add' := fun s t ↦ by
        apply section_ext U hU V.unop
        intro i
        change res N inf_le_left (glueSection U hU φ hφ V.unop (s + t)) =
          res N inf_le_left (glueSection U hU φ hφ V.unop s +
            glueSection U hU φ hφ V.unop t)
        simp only [map_add, res_glueSection] }
  naturality V W f := by
    ext s
    exact glueSection_res U hU φ hφ (leOfHom f.unop) s

/-- The additive gluing is linear, as witnessed after restriction to each chart. -/
def glue : M ⟶ N :=
  ⟨PresheafOfModules.homMk (glueAdditive U hU φ hφ) (fun V r s ↦ by
    obtain ⟨V⟩ := V
    change Γ(X, V) at r
    change Γ(M, V) at s
    change (glueAdditive U hU φ hφ).app (op V) (r • s) =
      (N.smul r).hom ((glueAdditive U hU φ hφ).app (op V) s)
    apply section_ext U hU V
    intro i
    change res N inf_le_left (glueSection U hU φ hφ V (r • s)) =
      res N inf_le_left (r • glueSection U hU φ hφ V s)
    simp only [res_glueSection, res, map_smul, map_smulₛₗ, RingHom.id_apply])⟩

/-- The glued morphism restricts to each supplied local morphism. -/
lemma glue_over (i : ι) : (glue U hU φ hφ).over (U i) = φ i := by
  apply SheafOfModules.hom_ext
  ext V s
  exact glueSection_of_le U hU φ hφ V.unop.left i (leOfHom V.unop.hom) s

/-- Maps of module sheaves agree if their restrictions to a cover agree. -/
lemma hom_ext (a b : M ⟶ N) (h : ∀ i, a.over (U i) = b.over (U i)) : a = b := by
  apply Scheme.Modules.hom_ext
  intro V
  ext s
  apply section_ext U hU V
  intro i
  have ha := congr($(a.mapPresheaf.naturality
    (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op) s)
  have hb := congr($(b.mapPresheaf.naturality
    (homOfLE (inf_le_left : V ⊓ U i ≤ V)).op) s)
  exact ha.symm.trans ((congrArg (fun c ↦ localApp c
    (inf_le_right : V ⊓ U i ≤ U i) (res M inf_le_left s)) (h i)).trans hb)

include hφ in
/-- Existence and uniqueness use only local maps and their overlap equalities. -/
theorem existsUnique_glue : ∃! a : M ⟶ N, ∀ i, a.over (U i) = φ i :=
  ⟨glue U hU φ hφ, glue_over U hU φ hφ,
    fun a ha ↦ hom_ext U hU a _ (fun i ↦ (ha i).trans (glue_over U hU φ hφ i).symm)⟩

/-- Gluing formulated directly for actual restrictions to open subschemes. -/
theorem existsUnique_glue_restrict
    (a : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (ha : Compatible U (fun i ↦ (restrictionEquiv (U i)).symm (a i))) :
    ∃! b : M ⟶ N, ∀ i, (restrictFunctor (U i).ι).map b = a i := by
  obtain ⟨b, hb, hu⟩ := existsUnique_glue U hU _ ha
  refine ⟨b, fun i ↦ ?_, fun c hc ↦ hu c (fun i ↦ ?_)⟩
  · rw [← restrictionEquiv_over, hb, Equiv.apply_symm_apply]
  · apply (restrictionEquiv (U i)).injective
    rw [restrictionEquiv_over, hc, Equiv.apply_symm_apply]

/-- A cover detects equality of maps using restrictions to open subschemes. -/
lemma hom_ext_restrict (a b : M ⟶ N)
    (h : ∀ i, (restrictFunctor (U i).ι).map a = (restrictFunctor (U i).ι).map b) :
    a = b := by
  apply hom_ext U hU
  intro i
  apply (restrictionEquiv (U i)).injective
  simpa only [restrictionEquiv_over] using h i

end FLT.Mazur.ModuleSheafMorphismGluing
