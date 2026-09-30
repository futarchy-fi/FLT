/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePullbackTrivializationCoherence
public import FLT.Mazur.ModuleSheafMorphismGluing

/-!
# Pullback of module sheaves descended from units

Inverse-image transition units determine a cocycle. The chosen local pullback
comparisons agree on overlaps, so their forward and inverse maps glue to an
isomorphism with the actual module-sheaf pullback.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

open Scheme.Modules

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.ModuleSheafMorphismGluing

variable {X : Scheme.{u}} {M N P : X.Modules}

private def restrictionStep (M : X.Modules) {V U : X.Opens} (h : V ≤ U) :
    M.restrict V.ι ≅ (M.restrict U.ι).restrict (X.homOfLE h) :=
  (restrictFunctorCongr (X.homOfLE_ι h).symm).app M ≪≫
    (restrictFunctorComp (X.homOfLE h) U.ι).app M

private def restrictMap {V U : X.Opens} (h : V ≤ U) (a : M.restrict U.ι ⟶ N.restrict U.ι) :
    M.restrict V.ι ⟶ N.restrict V.ι :=
  (restrictionStep M h).hom ≫ (restrictFunctor (X.homOfLE h)).map a ≫
    (restrictionStep N h).inv

private lemma restrictionEquiv_symm_app (U : X.Opens) (a : M.restrict U.ι ⟶ N.restrict U.ι)
    (W : U.toScheme.Opens) (s : Γ(M, U.ι ''ᵁ W)) :
    localApp ((restrictionEquiv U).symm a) (U.ι_image_le W) s = a.app W s :=
  congrArg (fun b ↦ b.app W s) ((restrictionEquiv U).apply_symm_apply a)

private lemma restrictMap_app {V U : X.Opens} (h : V ≤ U)
    (a : M.restrict U.ι ⟶ N.restrict U.ι) (W : V.toScheme.Opens)
    (s : Γ(M, V.ι ''ᵁ W)) :
    (restrictMap h a).app W s =
      localApp ((restrictionEquiv U).symm a) ((V.ι_image_le W).trans h) s := by
  let W' := X.homOfLE h ''ᵁ W
  have hCD : U.ι ''ᵁ W' ≤ V.ι ''ᵁ W := by
    dsimp [W']; simp only [← Scheme.Hom.comp_image, X.homOfLE_ι, le_refl]
  have hDC : V.ι ''ᵁ W ≤ U.ι ''ᵁ W' := by
    dsimp [W']; simp only [← Scheme.Hom.comp_image, X.homOfLE_ι, le_refl]
  simp only [restrictMap, restrictionStep, Iso.trans_hom, Iso.trans_inv, Iso.app_hom,
    Iso.app_inv, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    restrictFunctorCongr_hom_app_app, restrictFunctorCongr_inv_app_app,
    restrictFunctorComp_hom_app_app, restrictFunctorComp_inv_app_app]
  change N.presheaf.map _ (N.presheaf.map _ (a.app W'
    (M.presheaf.map _ (M.presheaf.map _ s)))) = _
  rw [← restrictionEquiv_symm_app U a W']
  change (N.presheaf.map _ ≫ N.presheaf.map _)
    (localApp ((restrictionEquiv U).symm a) (U.ι_image_le W')
      ((M.presheaf.map _ ≫ M.presheaf.map _) s)) = _
  rw [← Functor.map_comp, ← Functor.map_comp]
  change res N hDC (localApp ((restrictionEquiv U).symm a)
    (U.ι_image_le W') (res M hCD s)) = _
  rw [localApp_res _ hCD ((V.ι_image_le W).trans h), res_res, res_self]

private lemma compatible_of_restrictMap {ι : Type u} (U : ι → X.Opens)
    (a : ∀ i, M.restrict (U i).ι ⟶ N.restrict (U i).ι)
    (ha : ∀ i j, restrictMap (inf_le_left : U i ⊓ U j ≤ U i) (a i) =
      restrictMap (inf_le_right : U i ⊓ U j ≤ U j) (a j)) :
    Compatible U (fun i ↦ (restrictionEquiv (U i)).symm (a i)) := by
  intro i j V hi hj
  obtain ⟨W, rfl⟩ : ∃ W : (U i ⊓ U j).toScheme.Opens, (U i ⊓ U j).ι ''ᵁ W = V := by
    refine ⟨(U i ⊓ U j).ι ⁻¹ᵁ V, ?_⟩
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf]
    simp [inf_eq_right.mpr (le_inf hi hj)]
  ext s
  have hh := congrArg (fun b ↦ b.app W s) (ha i j)
  simpa only [restrictMap_app] using hh

private lemma restrictMap_trivializations {V U : X.Opens} (h : V ≤ U)
    (e : M.restrict U.ι ≅ FCurve.structureModule U.toScheme)
    (e' : N.restrict U.ι ≅ FCurve.structureModule U.toScheme) :
    restrictMap h (e.hom ≫ e'.inv) =
      (FCurve.ModuleSheafTensor.restrictTrivialization h e).hom ≫
        (FCurve.ModuleSheafTensor.restrictTrivialization h e').inv := by
  simp [restrictMap, restrictionStep, FCurve.ModuleSheafTensor.restrictTrivialization,
    Functor.map_comp, Category.assoc]

private lemma restrictionEquiv_comp (U : X.Opens) (a : M.over U ⟶ N.over U)
    (b : N.over U ⟶ P.over U) :
    restrictionEquiv U (a ≫ b) = restrictionEquiv U a ≫ restrictionEquiv U b := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

private lemma restrictionEquiv_id (U : X.Opens) :
    restrictionEquiv U (𝟙 (M.over U)) = 𝟙 (M.restrict U.ι) := by
  apply Scheme.Modules.hom_ext
  intro W
  ext s
  rfl

private lemma localApp_inverse (U : X.Opens) (e : M.restrict U.ι ≅ N.restrict U.ι)
    {V : X.Opens} (h : V ≤ U) (s : Γ(N, V)) :
    localApp ((restrictionEquiv U).symm e.hom) h
      (localApp ((restrictionEquiv U).symm e.inv) h s) = s := by
  have he : (restrictionEquiv U).symm e.inv ≫ (restrictionEquiv U).symm e.hom = 𝟙 _ := by
    apply (restrictionEquiv U).injective
    simp only [restrictionEquiv_comp, Equiv.apply_symm_apply,
      e.inv_hom_id, restrictionEquiv_id]
  exact congrArg (fun a ↦ localApp a h s) he

/-- Compatible local isomorphisms have compatible inverses. -/
lemma compatible_inverse {ι : Type u} (U : ι → X.Opens)
    (e : ∀ i, M.restrict (U i).ι ≅ N.restrict (U i).ι)
    (he : Compatible U (fun i ↦ (restrictionEquiv (U i)).symm (e i).hom)) :
    Compatible U (fun i ↦ (restrictionEquiv (U i)).symm (e i).inv) := by
  intro i j V hi hj
  ext s
  calc
    localApp ((restrictionEquiv (U i)).symm (e i).inv) hi s =
      localApp ((restrictionEquiv (U i)).symm (e i).inv) hi
        (localApp ((restrictionEquiv (U j)).symm (e j).hom) hj
          (localApp ((restrictionEquiv (U j)).symm (e j).inv) hj s)) := by
      rw [localApp_inverse]
    _ = localApp ((restrictionEquiv (U j)).symm (e j).inv) hj s := by
      rw [← he i j V hi hj]
      exact localApp_inverse (U i) (e i).symm hi _

/-- Glue compatible local isomorphisms and their inverses on an open cover. -/
def glueLocalIso {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ N.restrict (U i).ι)
    (he : Compatible U (fun i ↦ (restrictionEquiv (U i)).symm (e i).hom)) : M ≅ N := by
  let a := (existsUnique_glue_restrict U hU (fun i ↦ (e i).hom) he).choose
  have ha := (existsUnique_glue_restrict U hU (fun i ↦ (e i).hom) he).choose_spec.1
  let b := (existsUnique_glue_restrict U hU (fun i ↦ (e i).inv)
    (compatible_inverse U e he)).choose
  have hb := (existsUnique_glue_restrict U hU (fun i ↦ (e i).inv)
    (compatible_inverse U e he)).choose_spec.1
  refine ⟨a, b, hom_ext_restrict U hU _ _ (fun i ↦ ?_),
    hom_ext_restrict U hU _ _ (fun i ↦ ?_)⟩
  · rw [Functor.map_comp, ha, hb, CategoryTheory.Functor.map_id, (e i).hom_inv_id]
  · rw [Functor.map_comp, hb, ha, CategoryTheory.Functor.map_id, (e i).inv_hom_id]

private lemma glueLocalIso_hom_restrict {ι : Type u} (U : ι → X.Opens) (hU : iSup U = ⊤)
    (e : ∀ i, M.restrict (U i).ι ≅ N.restrict (U i).ι)
    (he : Compatible U (fun i ↦ (restrictionEquiv (U i)).symm (e i).hom)) (i : ι) :
    (restrictFunctor (U i).ι).map (glueLocalIso U hU e he).hom = (e i).hom :=
  (existsUnique_glue_restrict U hU (fun i ↦ (e i).hom) he).choose_spec.1 i

end FLT.Mazur.ModuleSheafMorphismGluing

namespace FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle
variable {X Y : Scheme.{u}} {ι : Type u} {U : ι → Y.Opens}
variable (g : Cocycle U) (f : X ⟶ Y)

/-- Pull an overlap unit to any open in the inverse-image overlap. -/
def inverseImageUnit (i j : ι) (V : X.Opens)
    (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j) : Γ(X, V)ˣ :=
  Units.map (f.appLE (U i ⊓ U j) V (le_inf hi hj)).hom.toMonoidHom
    (g.unit i j (U i ⊓ U j) inf_le_left inf_le_right)

/-- Inverse-image transition units commute with restriction. -/
lemma inverseImageUnit_natural (i j : ι) {V W : X.Opens} (h : W ≤ V)
    (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j) :
    res h (g.inverseImageUnit f i j V hi hj : Γ(X, V)) =
      g.inverseImageUnit f i j W (h.trans hi) (h.trans hj) := by
  change X.presheaf.map (homOfLE h).op (f.appLE _ _ _ _) = f.appLE _ _ _ _
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

/-- A repeated inverse-image chart has the identity transition. -/
lemma inverseImageUnit_refl (i : ι) (V : X.Opens) (hi : V ≤ f ⁻¹ᵁ U i) :
    g.inverseImageUnit f i i V hi hi = 1 := by
  simp [inverseImageUnit, g.refl]

/-- The inverse-image unit can be computed on any common source chart. -/
lemma inverseImageUnit_eq (i j : ι) (V : X.Opens)
    (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j)
    (A : Y.Opens) (hai : A ≤ U i) (haj : A ≤ U j) (hV : V ≤ f ⁻¹ᵁ A) :
    (g.inverseImageUnit f i j V hi hj : Γ(X, V)) =
      f.appLE A V hV (g.unit i j A hai haj : Γ(Y, A)) := by
  rw [← g.natural i j (le_inf hai haj) inf_le_left inf_le_right]
  change f.appLE _ _ _ _ = f.appLE _ _ _ (Y.presheaf.map _ _)
  rw [← CommRingCat.comp_apply, Scheme.Hom.map_appLE]

/-- The inverse-image units satisfy the cocycle identity. -/
lemma inverseImageUnit_cocycle (i j k : ι) (V : X.Opens)
    (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j) (hk : V ≤ f ⁻¹ᵁ U k) :
    g.inverseImageUnit f i j V hi hj * g.inverseImageUnit f j k V hj hk =
      g.inverseImageUnit f i k V hi hk := by
  let A := U i ⊓ U j ⊓ U k
  have hai : A ≤ U i := inf_le_left.trans inf_le_left
  have haj : A ≤ U j := inf_le_left.trans inf_le_right
  have hak : A ≤ U k := inf_le_right
  have hV : V ≤ f ⁻¹ᵁ A := le_inf (le_inf hi hj) hk
  apply Units.ext
  change (g.inverseImageUnit f i j V hi hj : Γ(X, V)) *
    (g.inverseImageUnit f j k V hj hk : Γ(X, V)) = _
  rw [g.inverseImageUnit_eq f i j V hi hj A hai haj hV,
    g.inverseImageUnit_eq f j k V hj hk A haj hak hV,
    g.inverseImageUnit_eq f i k V hi hk A hai hak hV, ← map_mul]
  exact congrArg (fun t : Γ(Y, A)ˣ ↦ f.appLE A V hV (t : Γ(Y, A)))
    (g.cocycle i j k A hai haj hak)

/-- The cocycle obtained by pulling back its overlap units. -/
def inverseImage : Cocycle (fun i ↦ f ⁻¹ᵁ U i) where
  unit := g.inverseImageUnit f
  natural := g.inverseImageUnit_natural f
  refl := g.inverseImageUnit_refl f
  cocycle := g.inverseImageUnit_cocycle f

/-- An inverse-image family is a cover whenever the original family is a cover. -/
lemma inverseImage_cover (hU : iSup U = ⊤) : (⨆ i, f ⁻¹ᵁ U i) = ⊤ := by
  rw [← Scheme.Hom.preimage_iSup, hU, Scheme.Hom.preimage_top]

/-- The comparison prescribed by the two chosen trivializations. -/
def localPullbackComparison (i : ι) :
    ((Scheme.Modules.pullback f).obj g.sheaf).restrict (f ⁻¹ᵁ U i).ι ≅
      (g.inverseImage f).sheaf.restrict (f ⁻¹ᵁ U i).ι :=
  modulePullbackTrivialization f (g.restrictIso i) ≪≫
    ((g.inverseImage f).restrictIso i).symm

open FLT.Mazur.ModuleSheafMorphismGluing
set_option maxRecDepth 2048 in
-- The overlap calculation compares nested restricted module structures.
/-- The local comparisons agree on every subopen of every overlap. -/
lemma localPullbackComparison_compatible :
    Compatible (fun i ↦ f ⁻¹ᵁ U i)
      (fun i ↦ (restrictionEquiv (f ⁻¹ᵁ U i)).symm
        (g.localPullbackComparison f i).hom) := by
  apply compatible_of_restrictMap
  intro i j
  let A := U i ⊓ U j
  have hi : A ≤ U i := inf_le_left
  have hj : A ≤ U j := inf_le_right
  simp only [localPullbackComparison, Iso.trans_hom, Iso.symm_hom]
  rw [restrictMap_trivializations, restrictMap_trivializations]
  let ei := ModuleSheafTensor.restrictTrivialization (f.preimage_mono hi)
    (modulePullbackTrivialization f (g.restrictIso i))
  let ej := ModuleSheafTensor.restrictTrivialization (f.preimage_mono hj)
    (modulePullbackTrivialization f (g.restrictIso j))
  let bi := ModuleSheafTensor.restrictTrivialization (f.preimage_mono hi)
    ((g.inverseImage f).restrictIso i)
  let bj := ModuleSheafTensor.restrictTrivialization (f.preimage_mono hj)
    ((g.inverseImage f).restrictIso j)
  change ei.hom ≫ bi.inv = ej.hom ≫ bj.inv
  have hb (k : ι) (hk : A ≤ U k) :
      ModuleSheafTensor.restrictTrivialization (f.preimage_mono hk)
        ((g.inverseImage f).restrictIso k) =
      (g.inverseImage f).onOpenIso k (f ⁻¹ᵁ A) (f.preimage_mono hk) :=
    (g.inverseImage f).restrictTrivialization_onOpenIso k (f.preimage_mono hk) le_rfl
  have hc : ej.inv ≫ ei.hom = bj.inv ≫ bi.hom := by
    apply Scheme.Modules.hom_ext
    intro W
    ext r
    have hW : W ≤ (f ∣_ A) ⁻¹ᵁ ⊤ := by simp
    dsimp only [ei, ej, bi, bj]
    rw [hb j hj, hb i hi, g.pullback_restrictIso_change f i j A hi hj ⊤ W hW r]
    erw [(g.inverseImage f).onOpenIso_change i j (f ⁻¹ᵁ A)
      (f.preimage_mono hi) (f.preimage_mono hj) W r]
    rw [morphismRestrict_appLE]
    congr 1
    exact (g.inverseImageUnit_eq f i j ((f ⁻¹ᵁ A).ι ''ᵁ W)
      (((f ⁻¹ᵁ A).ι_image_le W).trans (f.preimage_mono hi))
      (((f ⁻¹ᵁ A).ι_image_le W).trans (f.preimage_mono hj))
      (A.ι ''ᵁ ⊤) ((A.ι_image_le ⊤).trans hi) ((A.ι_image_le ⊤).trans hj)
      (((f ⁻¹ᵁ A).ι.image_mono hW).trans
        (image_morphismRestrict_preimage f A ⊤).le)).symm
  calc
    ei.hom ≫ bi.inv = ej.hom ≫ (ej.inv ≫ ei.hom) ≫ bi.inv := by simp [Category.assoc]
    _ = ej.hom ≫ (bj.inv ≫ bi.hom) ≫ bi.inv := by rw [hc]
    _ = ej.hom ≫ bj.inv := by simp [Category.assoc]

/-- The actual pullback is the sheaf descended from the inverse-image cocycle. -/
def pullbackIso (hU : iSup U = ⊤) :
    (Scheme.Modules.pullback f).obj g.sheaf ≅ (g.inverseImage f).sheaf :=
  glueLocalIso (fun i ↦ f ⁻¹ᵁ U i) (inverseImage_cover f hU)
    (g.localPullbackComparison f) (g.localPullbackComparison_compatible f)

/-- The global isomorphism restricts to the prescribed local comparison. -/
lemma pullbackIso_restrict (hU : iSup U = ⊤) (i : ι) :
    (restrictFunctor (f ⁻¹ᵁ U i).ι).mapIso (g.pullbackIso f hU) =
      g.localPullbackComparison f i := by
  apply Iso.ext
  exact glueLocalIso_hom_restrict (fun i ↦ f ⁻¹ᵁ U i) (inverseImage_cover f hU)
    (g.localPullbackComparison f) (g.localPullbackComparison_compatible f) i

/-- The global isomorphism identifies the two chosen local trivializations. -/
lemma pullbackIso_local (hU : iSup U = ⊤) (i : ι) :
    (restrictFunctor (f ⁻¹ᵁ U i).ι).mapIso (g.pullbackIso f hU) ≪≫
      (g.inverseImage f).restrictIso i = modulePullbackTrivialization f (g.restrictIso i) := by
  rw [g.pullbackIso_restrict]
  simp [localPullbackComparison]

/-- The global comparison has the prescribed transition coefficient on every common subopen. -/
lemma pullbackIso_change (hU : iSup U = ⊤) (i j : ι) (V : X.Opens)
    (hi : V ≤ f ⁻¹ᵁ U i) (hj : V ≤ f ⁻¹ᵁ U j) (W : V.toScheme.Opens)
    (r : Γ(V.toScheme, W)) :
    (((restrictFunctor V.ι).mapIso (g.pullbackIso f hU) ≪≫
        (g.inverseImage f).onOpenIso j V hj).inv ≫
      ((restrictFunctor V.ι).mapIso (g.pullbackIso f hU) ≪≫
        (g.inverseImage f).onOpenIso i V hi).hom).app W r =
    (g.inverseImageUnit f i j (V.ι ''ᵁ W) ((V.ι_image_le W).trans hi)
      ((V.ι_image_le W).trans hj) : Γ(X, V.ι ''ᵁ W)) *
        (show Γ(X, V.ι ''ᵁ W) from r) := by
  simp only [Iso.trans_inv, Iso.trans_hom, Category.assoc, Iso.inv_hom_id_assoc]
  exact (g.inverseImage f).onOpenIso_change i j V hi hj W r

end FLT.Mazur.FCurve.ModuleSheafUnitCocycle.Cocycle
