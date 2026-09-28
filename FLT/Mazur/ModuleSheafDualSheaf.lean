/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDual
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf
public import Mathlib.Topology.Sheaves.Module

/-!
# The intrinsic dual of a module sheaf

The additive internal Hom is a sheaf. Linearity on every subopen is a local
condition, so its subpresheaf of linear morphisms is also a sheaf. Comparing
slice sites with open subschemes proves the sheaf condition for the actual
dual presheaf. The resulting dual is contravariant and commutes with open restriction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} (M : X.Modules)

/-- Evaluate an additive local morphism on one subopen. -/
def moduleDualHomApp {U : X.Opens}
    (φ : (presheafHom M.presheaf (structureModule X).presheaf).obj (op U))
    (V : Over U) : Γ(M, V.left) →+ Γ(X, V.left) := (φ.app (op V)).hom

/-- Local additive morphisms that are linear on every subopen. -/
def moduleDualLinearHom :
    Subfunctor (presheafHom M.presheaf (structureModule X).presheaf) where
  obj U := { φ | ∀ (V : Over U.unop) (r : Γ(X, V.left)) (s : Γ(M, V.left)),
    moduleDualHomApp M φ V (r • s) = r * moduleDualHomApp M φ V s }
  map f _ hφ V r s := hφ ((Over.map f.unop).obj V) r s

/-- Linearity of a local additive morphism can be checked on a covering sieve. -/
lemma moduleDualLinearHom_local (U : X.Opensᵒᵖ)
    (φ : (presheafHom M.presheaf (structureModule X).presheaf).obj U)
    (hφ : (moduleDualLinearHom M).sieveOfSection φ ∈ Opens.grothendieckTopology X U.unop) :
    φ ∈ (moduleDualLinearHom M).obj U := by
  intro V r s
  have hG := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget Ab) (structureModule X).isSheaf)
  apply (hG _ ((Opens.grothendieckTopology X).pullback_stable V.hom hφ)).isSeparatedFor.ext
  intro W g hg
  let f : Over.mk (g ≫ V.hom) ⟶ V := Over.homMk g
  have hn (t : Γ(M, V.left)) :
      moduleDualHomApp M φ (Over.mk (g ≫ V.hom)) (M.presheaf.map g.op t) =
        X.presheaf.map g.op (moduleDualHomApp M φ V t) :=
    congr($(φ.naturality f.op) t)
  change X.presheaf.map g.op (moduleDualHomApp M φ V (r • s)) =
    X.presheaf.map g.op (r * moduleDualHomApp M φ V s)
  rw [map_mul, ← hn, ← hn, Scheme.Modules.map_smul]
  have hl := hg (Over.mk (𝟙 W)) (X.presheaf.map g.op r) (M.presheaf.map g.op s)
  dsimp only [moduleDualHomApp] at hl
  have he := presheafHom_map_app_op_mk_id (F := M.presheaf)
    (G := (structureModule X).presheaf) (g ≫ V.hom) φ
  erw [he] at hl
  exact hl

/-- Compatible local linear morphisms glue uniquely, and the glue remains linear. -/
lemma moduleDualLinearHom_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (moduleDualLinearHom M).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).mp
      ((structureModule X).isSheaf.hom M.presheaf))).mpr
  exact moduleDualLinearHom_local M

/-- The linear predicate is exactly a morphism of module sheaves on the slice site. -/
def moduleDualLinearHomEquiv (U : X.Opens) :
    (moduleDualLinearHom M).obj (op U) ≃
      (M.over U ⟶ SheafOfModules.unit (X.ringCatSheaf.over U)) where
  toFun φ := ⟨PresheafOfModules.homMk φ.1 (fun V r s ↦ φ.2 V.unop r s)⟩
  invFun φ := ⟨(PresheafOfModules.toPresheaf _).map φ.val,
    fun V r s ↦ (φ.val.app (op V)).hom.map_smul r s⟩
  left_inv φ := by rfl
  right_inv φ := by rfl

/-- Additive local morphisms can equally be indexed by opens of the open subscheme. -/
def moduleDualAddHomEquiv (U : X.Opens) :
    (presheafHom M.presheaf (structureModule X).presheaf).obj (op U) ≃
      ((M.restrict U.ι).presheaf ⟶ (structureModule U.toScheme).presheaf) :=
  (Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ Ab).obj U.overEquivalence.inverse.op)).homEquiv

/-- Restriction to an open uses the original scalar action on image opens. -/
lemma moduleDual_restrict_smul (U : X.Opens) (W : U.toScheme.Opens)
    (r : Γ(U.toScheme, W)) :
    (M.restrict U.ι).smul r = M.smul (U := U.ι ''ᵁ W) r := by
  change M.smul ((U.ι.appIso W).inv r) = _
  rw [Scheme.Opens.ι_appIso]
  rfl

/-- The comparison of indexing categories preserves and reflects linearity. -/
lemma moduleDualAddHomEquiv_linear (U : X.Opens)
    (φ : (presheafHom M.presheaf (structureModule X).presheaf).obj (op U)) :
    φ ∈ (moduleDualLinearHom M).obj (op U) ↔
      ∀ (W : U.toScheme.Opensᵒᵖ) (r : Γ(U.toScheme, W.unop))
        (s : Γ(M.restrict U.ι, W.unop)),
        (moduleDualAddHomEquiv M U φ).app W (r • s) =
          (((structureModule U.toScheme).val.obj W).smul r).hom
            ((moduleDualAddHomEquiv M U φ).app W s) := by
  constructor
  · intro h W r s
    change (φ.app (op (U.overEquivalence.inverse.obj W.unop)))
      (((M.restrict U.ι).smul r).hom s) = _
    rw [moduleDual_restrict_smul]
    exact h (U.overEquivalence.inverse.obj W.unop) r s
  · intro h V
    have he : U.overEquivalence.inverse.obj (U.overEquivalence.functor.obj V) = V := by
      refine CostructuredArrow.obj_ext _ _ ?_ (Subsingleton.elim _ _)
      exact (leOfHom (U.overEquivalence.unitIso.inv.app V).left).antisymm
        (leOfHom (U.overEquivalence.unitIso.hom.app V).left)
    rw [← he]
    intro r s
    have hh := h (op (U.overEquivalence.functor.obj V)) r s
    change (φ.app (op (U.overEquivalence.inverse.obj
      (U.overEquivalence.functor.obj V))))
        (((M.restrict U.ι).smul r).hom s) = _ at hh
    rw [moduleDual_restrict_smul] at hh
    exact hh

/-- Sections of the linear Hom sheaf are the actual dual sections of the module sheaf. -/
def moduleDualSectionsEquiv (U : X.Opens) :
    (moduleDualLinearHom M).obj (op U) ≃ ModuleDualSections M U where
  toFun φ := ⟨PresheafOfModules.homMk (moduleDualAddHomEquiv M U φ.1)
    ((moduleDualAddHomEquiv_linear M U φ.1).mp φ.2)⟩
  invFun φ := ⟨(moduleDualAddHomEquiv M U).symm φ.mapPresheaf, by
    apply (moduleDualAddHomEquiv_linear M U _).mpr
    rw [Equiv.apply_symm_apply]
    intro W r s
    exact φ.app_smul r s⟩
  left_inv φ := Subtype.ext ((moduleDualAddHomEquiv M U).symm_apply_apply φ.1)
  right_inv φ := by
    apply Scheme.Modules.hom_ext
    intro W
    exact NatTrans.congr_app ((moduleDualAddHomEquiv M U).apply_symm_apply φ.mapPresheaf)
      (op W)

/-- Evaluation of the section comparison on an open of the open subscheme. -/
@[simp]
lemma moduleDualSectionsEquiv_app (U : X.Opens)
    (φ : (moduleDualLinearHom M).obj (op U)) (W : U.toScheme.Opens) :
    (moduleDualSectionsEquiv M U φ).app W =
      φ.1.app (op (U.overEquivalence.inverse.obj W)) := rfl

/-- The section comparison intertwines the canonical restriction maps. -/
lemma moduleDualSectionsEquiv_restrict {U V : X.Opens} (h : V ≤ U)
    (φ : (moduleDualLinearHom M).obj (op U)) :
    moduleDualSectionsEquiv M V ((moduleDualLinearHom M).toFunctor.map (homOfLE h).op φ) =
      moduleDualRestrict M h (moduleDualSectionsEquiv M U φ) := by
  apply Scheme.Modules.hom_ext
  intro W
  let A := (Over.map (homOfLE h)).obj (V.overEquivalence.inverse.obj W)
  let B := U.overEquivalence.inverse.obj (X.homOfLE h ''ᵁ W)
  have e : B.left = A.left := by
    change U.ι ''ᵁ X.homOfLE h ''ᵁ W = V.ι ''ᵁ W
    simp [← Scheme.Hom.comp_image]
  let g : B ⟶ A := Over.homMk (eqToHom e)
  have hn := φ.1.naturality g.op
  rw [moduleDualRestrict_app_eq M h _ W _ rfl]
  change φ.1.app (op A) =
    M.presheaf.map (eqToHom e).op ≫ φ.1.app (op B) ≫
      (structureModule X).presheaf.map (eqToHom e.symm).op
  change M.presheaf.map (eqToHom e).op ≫ φ.1.app (op B) =
    φ.1.app (op A) ≫ (structureModule X).presheaf.map (eqToHom e).op at hn
  erw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp]
  simp

/-- The linear Hom sheaf and the underlying dual presheaf have the same sections. -/
def moduleDualTypesIso :
    (moduleDualLinearHom M).toFunctor ≅ moduleDualAddPresheaf M ⋙ forget Ab :=
  NatIso.ofComponents (fun U ↦ (moduleDualSectionsEquiv M U.unop).toIso)
    (fun f ↦ by
      ext φ
      exact moduleDualSectionsEquiv_restrict M (leOfHom f.unop) φ)

/-- The intrinsic module-valued dual presheaf satisfies the sheaf condition. -/
lemma moduleDualPresheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (moduleDualPresheaf M).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget Ab)
  exact (Presheaf.isSheaf_of_iso_iff (moduleDualTypesIso M)).mp
    (moduleDualLinearHom_isSheaf M)

/-- The dual sheaf, whose sections are morphisms of restricted module sheaves. -/
def moduleSheafDual : X.Modules :=
  ⟨moduleDualPresheaf M, moduleDualPresheaf_isSheaf M⟩

/-- Precomposition of dual sections commutes with restriction. -/
lemma moduleDualRestrict_precomp {N : X.Modules} (f : M ⟶ N)
    {U V : X.Opens} (h : V ≤ U) (φ : ModuleDualSections N U) :
    moduleDualRestrict M h ((Scheme.Modules.restrictFunctor U.ι).map f ≫ φ) =
      (Scheme.Modules.restrictFunctor V.ι).map f ≫ moduleDualRestrict N h φ := by
  apply Scheme.Modules.hom_ext
  intro W
  rw [moduleDualRestrict_app_eq M h _ W _ rfl]
  simp only [Scheme.Modules.Hom.comp_app]
  rw [moduleDualRestrict_app_eq N h φ W _ rfl]
  let g := (homOfLE (show U.ι ''ᵁ X.homOfLE h ''ᵁ W ≤ V.ι ''ᵁ W by
    simp [← Scheme.Hom.comp_image])).op
  change M.presheaf.map g ≫ (f.app _ ≫ φ.app _) ≫ _ =
    f.app _ ≫ N.presheaf.map g ≫ φ.app _ ≫ _
  have hn := f.mapPresheaf.naturality g
  change M.presheaf.map g ≫ f.app _ = f.app _ ≫ N.presheaf.map g at hn
  simp only [← Category.assoc]
  rw [hn]

/-- Duality acts contravariantly on module-sheaf morphisms. -/
def moduleSheafDualMap {N : X.Modules} (f : M ⟶ N) :
    moduleSheafDual N ⟶ moduleSheafDual M :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun φ ↦ (Scheme.Modules.restrictFunctor (Scheme.Opens.ι U.unop)).map f ≫ φ
          map_zero' := by simp
          map_add' := fun φ ψ ↦ Preadditive.comp_add _ _ _ _ φ ψ }
      naturality := fun U V g ↦ by
        ext φ : 2
        exact (moduleDualRestrict_precomp M f (leOfHom g.unop) φ).symm }
    (fun U r φ ↦ by
      apply Scheme.Modules.hom_ext
      intro W
      ext s
      rfl)⟩

/-- Evaluation of the dual map is precomposition with the restricted morphism. -/
@[simp]
lemma moduleSheafDualMap_app {N : X.Modules} (f : M ⟶ N) (U : X.Opens)
    (φ : ModuleDualSections N U) :
    (moduleSheafDualMap M f).app U φ =
      (Scheme.Modules.restrictFunctor U.ι).map f ≫ φ := rfl

@[simp]
lemma moduleSheafDualMap_id : moduleSheafDualMap M (𝟙 M) = 𝟙 (moduleSheafDual M) := by
  ext U φ : 3
  simp

@[simp]
lemma moduleSheafDualMap_comp {N P : X.Modules} (f : M ⟶ N) (g : N ⟶ P) :
    moduleSheafDualMap M (f ≫ g) = moduleSheafDualMap N g ≫ moduleSheafDualMap M f := by
  ext U φ : 3
  simp [Category.assoc]

/-- An isomorphism of module sheaves induces the contravariant dual isomorphism. -/
def moduleSheafDualIso {N : X.Modules} (e : M ≅ N) :
    moduleSheafDual N ≅ moduleSheafDual M where
  hom := moduleSheafDualMap M e.hom
  inv := moduleSheafDualMap N e.inv
  hom_inv_id := by rw [← moduleSheafDualMap_comp, e.inv_hom_id, moduleSheafDualMap_id]
  inv_hom_id := by rw [← moduleSheafDualMap_comp, e.hom_inv_id, moduleSheafDualMap_id]

/-- Subopens of an open subscheme correspond to subopens of its image in the scheme. -/
def moduleDualOpenOverEquiv (U : X.Opens) (W : U.toScheme.Opens) :
    Over W ≌ Over (U.ι ''ᵁ W) :=
  (Over.postEquiv (X := W) U.overEquivalence.symm).trans
    (Over.iteratedSliceEquiv (U.overEquivalence.inverse.obj W))

/-- Restricting local additive morphisms along an open inclusion is an equivalence. -/
def moduleDualOpenAddEquiv (U : X.Opens) (W : U.toScheme.Opens) :
    (presheafHom M.presheaf (structureModule X).presheaf).obj (op (U.ι ''ᵁ W)) ≃
      (presheafHom (M.restrict U.ι).presheaf
        (structureModule U.toScheme).presheaf).obj (op W) :=
  (Functor.FullyFaithful.ofFullyFaithful
    ((Functor.whiskeringLeft _ _ Ab).obj (moduleDualOpenOverEquiv U W).functor.op)).homEquiv

/-- The open-restriction equivalence preserves and reflects local linearity. -/
lemma moduleDualOpenAddEquiv_linear (U : X.Opens) (W : U.toScheme.Opens)
    (φ : (presheafHom M.presheaf (structureModule X).presheaf).obj (op (U.ι ''ᵁ W))) :
    φ ∈ (moduleDualLinearHom M).obj (op (U.ι ''ᵁ W)) ↔
      moduleDualOpenAddEquiv M U W φ ∈ (moduleDualLinearHom (M.restrict U.ι)).obj (op W) := by
  constructor
  · intro h V r s
    change φ.app (op ((moduleDualOpenOverEquiv U W).functor.obj V))
      (((M.restrict U.ι).smul r).hom s) = _
    rw [moduleDual_restrict_smul]
    exact h ((moduleDualOpenOverEquiv U W).functor.obj V) r s
  · intro h V
    let E := moduleDualOpenOverEquiv U W
    have he : E.functor.obj (E.inverse.obj V) = V := by
      refine CostructuredArrow.obj_ext _ _ ?_ (Subsingleton.elim _ _)
      exact (leOfHom (E.counitIso.hom.app V).left).antisymm
        (leOfHom (E.counitIso.inv.app V).left)
    rw [← he]
    intro r s
    have hh := h (E.inverse.obj V) r s
    change φ.app (op (E.functor.obj (E.inverse.obj V)))
      (((M.restrict U.ι).smul r).hom s) = _ at hh
    rw [moduleDual_restrict_smul] at hh
    exact hh

/-- The linear local Hom commutes with restriction to an open subscheme. -/
def moduleDualOpenLinearEquiv (U : X.Opens) (W : U.toScheme.Opens) :
    (moduleDualLinearHom M).obj (op (U.ι ''ᵁ W)) ≃
      (moduleDualLinearHom (M.restrict U.ι)).obj (op W) :=
  (moduleDualOpenAddEquiv M U W).subtypeEquiv (moduleDualOpenAddEquiv_linear M U W)

/-- The canonical comparison between dual sections on an open and on its image. -/
def moduleDualOpenSectionsEquiv (U : X.Opens) (W : U.toScheme.Opens) :
    ModuleDualSections M (U.ι ''ᵁ W) ≃ ModuleDualSections (M.restrict U.ι) W :=
  (moduleDualSectionsEquiv M (U.ι ''ᵁ W)).symm.trans
    ((moduleDualOpenLinearEquiv M U W).trans (moduleDualSectionsEquiv (M.restrict U.ι) W))

/-- Addition of local linear morphisms. -/
def moduleDualLinearAdd {U : X.Opens}
    (φ ψ : (moduleDualLinearHom M).obj (op U)) :
    (moduleDualLinearHom M).obj (op U) :=
  ⟨{ app V := φ.1.app V + ψ.1.app V
     naturality := fun V Z f ↦ by
       simp only [Preadditive.comp_add, Preadditive.add_comp,
         φ.1.naturality f, ψ.1.naturality f] }, fun V r s ↦ by
    change moduleDualHomApp M φ.1 V (r • s) + moduleDualHomApp M ψ.1 V (r • s) = _
    rw [φ.2 V r s, ψ.2 V r s]
    exact (mul_add _ _ _).symm⟩

/-- Multiplication of local linear morphisms by a function on their domain. -/
def moduleDualLinearSMul {U : X.Opens} (r : Γ(X, U))
    (φ : (moduleDualLinearHom M).obj (op U)) :
    (moduleDualLinearHom M).obj (op U) :=
  ⟨{ app V := AddCommGrpCat.ofHom
      { toFun := fun s ↦ X.presheaf.map V.unop.hom.op r * moduleDualHomApp M φ.1 V.unop s
        map_zero' := by simp
        map_add' := by intros; simp [mul_add] }
     naturality := fun V Z f ↦ by
       ext s
       have hn := congr($(φ.1.naturality f) s)
       change moduleDualHomApp M φ.1 Z.unop (M.presheaf.map f.unop.left.op s) =
         X.presheaf.map f.unop.left.op (moduleDualHomApp M φ.1 V.unop s) at hn
       change X.presheaf.map Z.unop.hom.op r *
         moduleDualHomApp M φ.1 Z.unop (M.presheaf.map f.unop.left.op s) =
           X.presheaf.map f.unop.left.op
             (X.presheaf.map V.unop.hom.op r * moduleDualHomApp M φ.1 V.unop s)
       rw [map_mul, hn]
       congr 1
       exact congr($(X.presheaf.map_comp V.unop.hom.op f.unop.left.op) r) },
    fun V a s ↦ by
      change X.presheaf.map V.hom.op r * moduleDualHomApp M φ.1 V (a • s) =
        a * (X.presheaf.map V.hom.op r * moduleDualHomApp M φ.1 V s)
      rw [φ.2 V a s]
      exact mul_left_comm _ _ _⟩

@[simp]
lemma moduleDualSectionsEquiv_add {U : X.Opens}
    (φ ψ : (moduleDualLinearHom M).obj (op U)) :
    moduleDualSectionsEquiv M U (moduleDualLinearAdd M φ ψ) =
      moduleDualSectionsEquiv M U φ + moduleDualSectionsEquiv M U ψ := by
  ext W s
  rfl

@[simp]
lemma moduleDualSectionsEquiv_smul {U : X.Opens} (r : Γ(X, U))
    (φ : (moduleDualLinearHom M).obj (op U)) :
    moduleDualSectionsEquiv M U (moduleDualLinearSMul M r φ) =
      r • moduleDualSectionsEquiv M U φ := by
  ext W s
  simp only [moduleDualSections_smul_app, Scheme.Opens.ι_appIso, Iso.refl_hom]
  rfl

lemma moduleDualOpenLinearEquiv_add (U : X.Opens) (W : U.toScheme.Opens)
    (φ ψ : (moduleDualLinearHom M).obj (op (U.ι ''ᵁ W))) :
    moduleDualOpenLinearEquiv M U W (moduleDualLinearAdd M φ ψ) =
      moduleDualLinearAdd (M.restrict U.ι) (moduleDualOpenLinearEquiv M U W φ)
        (moduleDualOpenLinearEquiv M U W ψ) := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  ext s
  rfl

lemma moduleDualOpenSectionsEquiv_add (U : X.Opens) (W : U.toScheme.Opens)
    (φ ψ : ModuleDualSections M (U.ι ''ᵁ W)) :
    moduleDualOpenSectionsEquiv M U W (φ + ψ) =
      moduleDualOpenSectionsEquiv M U W φ + moduleDualOpenSectionsEquiv M U W ψ := by
  obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv M (U.ι ''ᵁ W)).surjective φ
  obtain ⟨ψ, rfl⟩ := (moduleDualSectionsEquiv M (U.ι ''ᵁ W)).surjective ψ
  rw [← moduleDualSectionsEquiv_add]
  simp only [moduleDualOpenSectionsEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [moduleDualOpenLinearEquiv_add, moduleDualSectionsEquiv_add]

lemma moduleDualOpenLinearEquiv_smul (U : X.Opens) (W : U.toScheme.Opens)
    (r : Γ(U.toScheme, W)) (φ : (moduleDualLinearHom M).obj (op (U.ι ''ᵁ W))) :
    moduleDualOpenLinearEquiv M U W (moduleDualLinearSMul M r φ) =
      moduleDualLinearSMul (M.restrict U.ι) r (moduleDualOpenLinearEquiv M U W φ) := by
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  ext s
  rfl

lemma moduleDualOpenSectionsEquiv_smul (U : X.Opens) (W : U.toScheme.Opens)
    (r : Γ(U.toScheme, W)) (φ : ModuleDualSections M (U.ι ''ᵁ W)) :
    moduleDualOpenSectionsEquiv M U W (moduleDualSMul M (U.ι ''ᵁ W) r φ) =
      moduleDualSMul (M.restrict U.ι) W r (moduleDualOpenSectionsEquiv M U W φ) := by
  obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv M (U.ι ''ᵁ W)).surjective φ
  refine (congrArg (moduleDualOpenSectionsEquiv M U W)
    (moduleDualSectionsEquiv_smul M (U := U.ι ''ᵁ W) r φ).symm).trans ?_
  simp only [moduleDualOpenSectionsEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [moduleDualOpenLinearEquiv_smul]
  exact moduleDualSectionsEquiv_smul (M.restrict U.ι) r _

lemma moduleDualOpenSectionsEquiv_restrict (U : X.Opens) {W Z : U.toScheme.Opens}
    (h : Z ≤ W) (φ : ModuleDualSections M (U.ι ''ᵁ W)) :
    moduleDualOpenSectionsEquiv M U Z (moduleDualRestrict M (U.ι.image_mono h) φ) =
      moduleDualRestrict (M.restrict U.ι) h (moduleDualOpenSectionsEquiv M U W φ) := by
  obtain ⟨φ, rfl⟩ := (moduleDualSectionsEquiv M (U.ι ''ᵁ W)).surjective φ
  rw [← moduleDualSectionsEquiv_restrict]
  simp only [moduleDualOpenSectionsEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]
  rw [← moduleDualSectionsEquiv_restrict]
  rfl

/-- Duality commutes canonically with restriction to an open subscheme. -/
def moduleSheafDualRestrictIso (U : X.Opens) :
    (moduleSheafDual M).restrict U.ι ≅ moduleSheafDual (M.restrict U.ι) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W ↦ ?_) ?_)
  · refine ModuleCat.isoMk
      (AddEquiv.toAddCommGrpIso
        { __ := moduleDualOpenSectionsEquiv M U W.unop
          map_add' := moduleDualOpenSectionsEquiv_add M U W.unop }) ?_
    intro r
    ext φ
    change moduleDualSMul (M.restrict U.ι) W.unop r
      (moduleDualOpenSectionsEquiv M U W.unop φ) =
      moduleDualOpenSectionsEquiv M U W.unop
        ((((moduleSheafDual M).restrict U.ι).smul r).hom φ)
    rw [moduleDual_restrict_smul]
    exact (moduleDualOpenSectionsEquiv_smul M U W.unop r φ).symm
  · intro W Z f
    ext φ
    exact moduleDualOpenSectionsEquiv_restrict M U (leOfHom f.unop) φ

end FLT.Mazur.FCurve
