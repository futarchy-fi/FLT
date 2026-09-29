/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Gluing objects of the category of module sheaves

Sections are families of sections of the chart pushforwards agreeing under the
transition maps on every subopen of an overlap. The ambient ring acts through
its restrictions to the charts. The sheaf condition is proved componentwise.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.ModuleSheafMorphismGluing

universe u

namespace FLT.Mazur.ModuleSheafGluing

variable {X : Scheme.{u}} {ι : Type u} (U : ι → X.Opens)

/-- Sectionwise bijectivity on subopens detects isomorphisms of restrictions. -/
lemma isIso_restrict_of_bijective {M N : X.Modules} (f : M ⟶ N) (V : X.Opens)
    (hf : ∀ W : X.Opens, W ≤ V → Function.Bijective (f.app W)) :
    IsIso ((restrictFunctor V.ι).map f) := by
  rw [Scheme.Modules.Hom.isIso_iff_isIso_app]
  intro W
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  exact hf (V.ι ''ᵁ W) (V.ι_image_le W)

/-- Actual chart modules with linear transition isomorphisms and their cocycle. -/
structure Data where
  /-- The module sheaf on each open chart. -/
  obj (i : ι) : (U i).toScheme.Modules
  /-- Linear transition isomorphisms on the ambient slice over each overlap. -/
  transition (i j : ι) :
    ((pushforward (U i).ι).obj (obj i)).over (U i ⊓ U j) ≅
      ((pushforward (U j).ι).obj (obj j)).over (U i ⊓ U j)
  /-- Transitions compose on every subopen of a triple overlap. -/
  cocycle (i j k : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j)
      (hk : V ≤ U k) (s) :
    localApp (transition j k).hom (le_inf hj hk)
      (localApp (transition i j).hom (le_inf hi hj) s) =
        localApp (transition i k).hom (le_inf hi hk) s

namespace Data

variable {U} (D : Data U)

/-- Extend a chart module to ambient opens by pushforward. -/
abbrev chart (i : ι) : X.Modules := (pushforward (U i).ι).obj (D.obj i)

/-- Transition on a subopen of an overlap. -/
abbrev trans (i j : ι) {V : X.Opens} (hi : V ≤ U i) (hj : V ≤ U j) :=
  localApp (D.transition i j).hom (le_inf hi hj)

/-- Identity transitions follow from invertibility and the cocycle. -/
lemma identity (i : ι) (V : X.Opens) (h : V ≤ U i) (s : Γ(D.chart i, V)) :
    D.trans i i h h s = s := by
  have hinv (t : Γ(D.chart i, V)) :
      localApp (D.transition i i).inv (le_inf h h) (D.trans i i h h t) = t :=
    congrArg (fun f ↦ localApp f (le_inf h h) t) (D.transition i i).hom_inv_id
  have hc := congrArg (localApp (D.transition i i).inv (le_inf h h))
    (D.cocycle i i i V h h h s)
  exact (hinv (D.trans i i h h s)).symm.trans (hc.trans (hinv s))

/-- Compatible families form a module over the ambient ring of sections. -/
def families (W : X.Opens) : Submodule Γ(X, W) (∀ i, Γ(D.chart i, W)) where
  carrier := {s | ∀ i j V (hV : V ≤ W) (hi : V ≤ U i) (hj : V ≤ U j),
    D.trans i j hi hj (res (D.chart i) hV (s i)) = res (D.chart j) hV (s j)}
  zero_mem' := by
    intro i j V hV hi hj
    simp only [Pi.zero_apply, map_zero]
  add_mem' := by
    intro s t hs ht i j V hV hi hj
    simp only [Pi.add_apply, map_add, hs i j V hV hi hj, ht i j V hV hi hj]
  smul_mem' := by
    intro r s hs i j V hV hi hj
    simp only [Pi.smul_apply, res,
      Scheme.Modules.map_smul, map_smulₛₗ, RingHom.id_apply]
    exact congrArg (_ • ·) (hs i j V hV hi hj)

/-- Restriction of a compatible family is componentwise restriction. -/
def restrict {V W : X.Opens} (h : V ≤ W) : D.families W →+ D.families V where
  toFun s := ⟨fun i ↦ res (D.chart i) h (s.val i), by
    intro i j T hT hi hj
    simpa only [res_res] using s.property i j T (hT.trans h) hi hj⟩
  map_zero' := by ext i; exact map_zero _
  map_add' s t := by ext i; exact map_add _ _ _

/-- The presheaf of compatible additive families. -/
def familyPresheaf : TopCat.Presheaf Ab X where
  obj W := AddCommGrpCat.of (D.families W.unop)
  map f := AddCommGrpCat.ofHom (D.restrict (leOfHom f.unop))
  map_id W := by ext s i; exact res_self _ _ _
  map_comp f g := by ext s i; exact (res_res _ _ _ _).symm

/-- Unique gluing of families follows from unique gluing on each chart. -/
lemma familyPresheaf_isSheaf : D.familyPresheaf.IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing _).mpr
  intro κ W s hs
  have hc (i : ι) : TopCat.Presheaf.IsCompatible (D.chart i).presheaf W
      (fun a ↦ (s a).val i) := fun a b ↦ congrArg (fun t ↦ t.val i) (hs a b)
  choose t ht hu using fun i ↦
    (D.chart i).isSheaf.isSheafUniqueGluing W (fun a ↦ (s a).val i) (hc i)
  have ht' (i : ι) (a : κ) : res (D.chart i) (le_iSup W a) (t i) = (s a).val i := ht i a
  have hmem : t ∈ D.families (iSup W) := by
    intro i j V hV hi hj
    apply TopCat.Sheaf.eq_of_locally_eq'
      (⟨(D.chart j).presheaf, (D.chart j).isSheaf⟩ : TopCat.Sheaf Ab X)
      (fun a ↦ V ⊓ W a) V (fun _ ↦ homOfLE inf_le_left)
      (by rw [← inf_iSup_eq]; exact le_inf le_rfl hV)
    intro a
    change res (D.chart j) inf_le_left (D.trans i j hi hj (res _ hV (t i))) = _
    rw [← localApp_res, res_res, res_res]
    have hi' := congrArg (res (D.chart i) (inf_le_right : V ⊓ W a ≤ W a)) (ht' i a)
    have hj' := congrArg (res (D.chart j) (inf_le_right : V ⊓ W a ≤ W a)) (ht' j a)
    rw [res_res] at hi' hj'
    rw [hi', hj']
    exact (s a).property i j _ inf_le_right (inf_le_left.trans hi) (inf_le_left.trans hj)
  refine ⟨⟨t, hmem⟩, fun a ↦ ?_, fun q hq ↦ ?_⟩
  · exact Subtype.ext (funext fun i ↦ ht' i a)
  · apply Subtype.ext
    funext i
    exact hu i (q.val i) (fun a ↦ congrArg (fun z ↦ z.val i) (hq a))

instance familyPresheafModule (W : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj W) (D.familyPresheaf.obj W) :=
  inferInstanceAs (Module Γ(X, W.unop) (D.families W.unop))

/-- The module sheaf constructed from compatible chart sections. -/
def glued : X.Modules where
  val := PresheafOfModules.ofPresheaf D.familyPresheaf (fun {_ _} f r s ↦ by
    apply Subtype.ext
    funext i
    exact (D.chart i).map_smul f.unop r (s.val i))
  isSheaf := D.familyPresheaf_isSheaf

/-- The ambient scalar acts through its restriction to each open chart. -/
lemma smul_component (W : X.Opens) (r : Γ(X, W)) (s : Γ(D.glued, W)) (i : ι) :
    (r • s).val i = ((D.obj i).smul (U := (U i).ι ⁻¹ᵁ W)
      ((U i).ι.app W r)).hom (s.val i) := rfl

/-- Projection to one chart pushforward. -/
def projection (i : ι) : D.glued ⟶ D.chart i :=
  ⟨PresheafOfModules.homMk
    { app := fun _ ↦ AddCommGrpCat.ofHom
        { toFun := fun s ↦ s.val i, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }
    (fun _ _ _ ↦ rfl)⟩

/-- The projections recover the prescribed transition isomorphisms. -/
lemma projection_transition (i j : ι) :
    (D.projection i).over (U i ⊓ U j) ≫ (D.transition i j).hom =
      (D.projection j).over (U i ⊓ U j) := by
  apply SheafOfModules.hom_ext
  ext V s
  have h := s.property i j V.unop.left le_rfl
    ((leOfHom V.unop.hom).trans inf_le_left) ((leOfHom V.unop.hom).trans inf_le_right)
  change D.trans i j ((leOfHom V.unop.hom).trans inf_le_left)
    ((leOfHom V.unop.hom).trans inf_le_right) (s.val i) = s.val j
  change D.trans i j ((leOfHom V.unop.hom).trans inf_le_left)
    ((leOfHom V.unop.hom).trans inf_le_right)
    ((D.chart i).presheaf.map (𝟙 (op V.unop.left)) (s.val i)) =
    (D.chart j).presheaf.map (𝟙 (op V.unop.left)) (s.val j) at h
  rw [(D.chart i).presheaf.map_id, (D.chart j).presheaf.map_id] at h
  exact h

/-- A chart pushforward ignores the part of an open outside its chart. -/
lemma chartRestriction_isIso (i : ι) (W : X.Opens) :
    IsIso ((D.chart i).presheaf.map
      (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op) := by
  have he : (U i).ι ⁻¹ᵁ (W ⊓ U i) = (U i).ι ⁻¹ᵁ W := by
    rw [Scheme.Hom.preimage_inf, Scheme.Opens.ι_preimage_self, inf_top_eq]
  change IsIso ((D.obj i).presheaf.map
    ((Opens.map (U i).ι.base).map (homOfLE inf_le_left)).op)
  have hh : ((Opens.map (U i).ι.base).map
      (homOfLE (inf_le_left : W ⊓ U i ≤ W))).op = (eqToHom he).op :=
    Subsingleton.elim _ _
  rw [hh]
  infer_instance

/-- Extend a chart section across the complement of its chart. -/
def extend (i : ι) (W : X.Opens) : Γ(D.chart i, W ⊓ U i) →+ Γ(D.chart i, W) :=
  letI _hIso := D.chartRestriction_isIso i W
  (inv ((D.chart i).presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op)).hom

lemma res_extend (i : ι) (W : X.Opens) (s : Γ(D.chart i, W ⊓ U i)) :
    res (D.chart i) inf_le_left (D.extend i W s) = s := by
  let _hIso := D.chartRestriction_isIso i W
  exact ConcreteCategory.congr_hom (IsIso.inv_hom_id
    ((D.chart i).presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op)) s

lemma extend_res (i : ι) (W : X.Opens) (s : Γ(D.chart i, W)) :
    D.extend i W (res (D.chart i) inf_le_left s) = s := by
  let _hIso := D.chartRestriction_isIso i W
  exact ConcreteCategory.congr_hom (IsIso.hom_inv_id
    ((D.chart i).presheaf.map (homOfLE (inf_le_left : W ⊓ U i ≤ W)).op)) s

/-- A chart section determines each component of its glued family. -/
def localFamily (i : ι) {W : X.Opens} (hW : W ≤ U i) (s : Γ(D.chart i, W))
    (j : ι) : Γ(D.chart j, W) :=
  D.extend j W (D.trans i j (inf_le_left.trans hW) inf_le_right
    (res (D.chart i) inf_le_left s))

lemma res_localFamily (i j : ι) {W V : X.Opens} (hW : W ≤ U i) (hV : V ≤ W)
    (hj : V ≤ U j) (s : Γ(D.chart i, W)) :
    res (D.chart j) hV (D.localFamily i hW s j) =
      D.trans i j (hV.trans hW) hj (res (D.chart i) hV s) := by
  have h := congrArg (res (D.chart j) (le_inf hV hj))
    (D.res_extend j W (D.trans i j (inf_le_left.trans hW) inf_le_right
      (res (D.chart i) inf_le_left s)))
  simpa only [localFamily, res_res, ← localApp_res] using h

lemma localFamily_mem (i : ι) {W : X.Opens} (hW : W ≤ U i) (s : Γ(D.chart i, W)) :
    D.localFamily i hW s ∈ D.families W := by
  intro j k V hV hj hk
  rw [D.res_localFamily i j hW hV hj, D.res_localFamily i k hW hV hk]
  exact D.cocycle i j k V (hV.trans hW) hj hk _

lemma localFamily_self (i : ι) {W : X.Opens} (hW : W ≤ U i) (s : Γ(D.chart i, W)) :
    D.localFamily i hW s i = s := by
  have h := D.res_localFamily i i hW le_rfl hW s
  calc
    D.localFamily i hW s i = D.trans i i hW hW s := by
      simpa only [res_self] using h
    _ = s := D.identity i W hW s

/-- Projection to a chart is bijective on every subopen of that chart. -/
lemma projection_bijective (i : ι) (W : X.Opens) (hW : W ≤ U i) :
    Function.Bijective ((D.projection i).app W) := by
  change Function.Bijective (fun s : D.families W ↦ s.val i)
  constructor
  · intro s t h
    apply Subtype.ext
    funext j
    let _hIso := D.chartRestriction_isIso j W
    apply (ConcreteCategory.bijective_of_isIso
      ((D.chart j).presheaf.map (homOfLE (inf_le_left : W ⊓ U j ≤ W)).op)).injective
    exact (s.property i j _ inf_le_left (inf_le_left.trans hW) inf_le_right).symm.trans
      ((congrArg (fun z ↦ D.trans i j (inf_le_left.trans hW) inf_le_right
        (res (D.chart i) inf_le_left z)) h).trans
          (t.property i j _ inf_le_left (inf_le_left.trans hW) inf_le_right))
  · intro s
    exact ⟨⟨D.localFamily i hW s, D.localFamily_mem i hW s⟩, D.localFamily_self i hW s⟩

/-- Restricting a projection to its chart gives an isomorphism. -/
lemma restrictionProjection_isIso (i : ι) :
    IsIso ((restrictFunctor (U i).ι).map (D.projection i)) :=
  isIso_restrict_of_bijective (D.projection i) (U i) (D.projection_bijective i)

/-- The glued sheaf restricts to the original module on each open chart. -/
def restrictionIso (i : ι) : D.glued.restrict (U i).ι ≅ D.obj i :=
  @asIso _ _ _ _ ((restrictFunctor (U i).ι).map (D.projection i))
    (D.restrictionProjection_isIso i) ≪≫
      (restrictFunctorAdjCounitIso (U i).ι).app (D.obj i)

/-- Compatible maps of the original chart modules. -/
structure Map (E : Data U) where
  /-- A module morphism on each original chart. -/
  app (i : ι) : D.obj i ⟶ E.obj i
  /-- Chart morphisms intertwine the transition isomorphisms. -/
  compatible (i j : ι) (V : X.Opens) (hi : V ≤ U i) (hj : V ≤ U j) (s) :
    E.trans i j hi hj (((pushforward (U i).ι).map (app i)).app V s) =
      ((pushforward (U j).ι).map (app j)).app V (D.trans i j hi hj s)

namespace Map

variable {D} {E F : Data U} (a : D.Map E)

/-- The map between chart pushforwards induced by a chart map. -/
abbrev chartMap (i : ι) : D.chart i ⟶ E.chart i := (pushforward (U i).ι).map (a.app i)

lemma chartMap_res (i : ι) {V W : X.Opens} (h : V ≤ W) (s : Γ(D.chart i, W)) :
    (a.chartMap i).app V (res (D.chart i) h s) =
      res (E.chart i) h ((a.chartMap i).app W s) :=
  congr($((a.chartMap i).mapPresheaf.naturality (homOfLE h).op) s)

/-- Applying compatible chart maps preserves compatible families. -/
def family (W : X.Opens) (s : D.families W) : E.families W :=
  ⟨fun i ↦ (a.chartMap i).app W (s.val i), by
    intro i j V hV hi hj
    rw [← a.chartMap_res, ← a.chartMap_res, a.compatible, s.property i j V hV hi hj]⟩

/-- The induced map on the slice over a chart. -/
def localMap (i : ι) : D.glued.over (U i) ⟶ E.glued.over (U i) :=
  ⟨PresheafOfModules.homMk
    { app := fun V ↦ AddCommGrpCat.ofHom
        { toFun := a.family V.unop.left
          map_zero' := by
            apply Subtype.ext
            funext j
            exact map_zero _
          map_add' := fun s t ↦ by
            apply Subtype.ext
            funext j
            exact map_add _ _ _ }
      naturality := fun V W f ↦ by
        ext s
        apply Subtype.ext
        funext j
        exact a.chartMap_res j (leOfHom f.unop.left) (s.val j) }
    (fun V r s ↦ by
      apply Subtype.ext
      funext j
      exact (a.chartMap j).app_smul r (s.val j))⟩

/-- The local maps agree on overlaps as maps of actual glued modules. -/
lemma localMap_compatible : Compatible U a.localMap := by
  intro i j V hi hj
  rfl

/-- Glue the induced local maps by module-sheaf morphism gluing. -/
def gluedMap (hU : iSup U = ⊤) : D.glued ⟶ E.glued :=
  glue U hU a.localMap a.localMap_compatible

lemma gluedMap_over (hU : iSup U = ⊤) (i : ι) :
    (a.gluedMap hU).over (U i) = a.localMap i :=
  glue_over U hU a.localMap a.localMap_compatible i

/-- The glued map acts componentwise on compatible families. -/
lemma gluedMap_app (hU : iSup U = ⊤) (W : X.Opens) (s : Γ(D.glued, W)) :
    (a.gluedMap hU).app W s = a.family W s := by
  apply section_ext U hU W
  intro i
  change res E.glued inf_le_left
    (glueSection U hU a.localMap a.localMap_compatible W s) = _
  rw [res_glueSection]
  apply Subtype.ext
  funext j
  exact a.chartMap_res j inf_le_left (s.val j)

/-- The glued map commutes with each chart projection. -/
lemma gluedMap_projection (hU : iSup U = ⊤) (i : ι) :
    a.gluedMap hU ≫ E.projection i = D.projection i ≫ a.chartMap i := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  exact congrArg (fun t ↦ t.val i) (a.gluedMap_app hU W s)

/-- Identity chart maps are compatible. -/
def id (D : Data U) : D.Map D where
  app i := 𝟙 (D.obj i)
  compatible := by intros; rfl

/-- Composition of compatible chart maps. -/
def comp (b : E.Map F) : D.Map F where
  app i := a.app i ≫ b.app i
  compatible i j V hi hj s := by
    change F.trans i j hi hj ((b.chartMap i).app V ((a.chartMap i).app V s)) =
      (b.chartMap j).app V ((a.chartMap j).app V (D.trans i j hi hj s))
    rw [b.compatible, a.compatible]

@[simp]
lemma gluedMap_id (hU : iSup U = ⊤) : (id D).gluedMap hU = 𝟙 D.glued := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  exact (id D).gluedMap_app hU W s

@[simp]
lemma gluedMap_comp (b : E.Map F) (hU : iSup U = ⊤) :
    (a.comp b).gluedMap hU = a.gluedMap hU ≫ b.gluedMap hU := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  change ((a.comp b).gluedMap hU).app W s =
    (b.gluedMap hU).app W ((a.gluedMap hU).app W s)
  rw [(a.comp b).gluedMap_app, b.gluedMap_app, a.gluedMap_app]
  rfl

end Map

end Data

end FLT.Mazur.ModuleSheafGluing
