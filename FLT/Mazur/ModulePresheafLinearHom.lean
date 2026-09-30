/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Sites.SheafHom
public import Mathlib.CategoryTheory.Sites.Subsheaf

/-!
# Linear Hom from a module presheaf to a module sheaf

Sections on an open are linear morphisms on its slice site. The additive Hom
sheaf contains these as a subfunctor defined by a local linearity condition.
Scalars act by restriction to each subopen, giving an actual module sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve.ModulePresheafLinearHom

variable {X : Scheme.{u}} (M : X.PresheafOfModules) (N : X.Modules)

/-- Local module morphisms, indexed by subopens of the given open. -/
abbrev Sections (U : X.Opens) :=
  (PresheafOfModules.pushforward₀ (Over.forget U) X.ringCatSheaf.obj).obj M ⟶
    (N.over U).val

/-- Evaluation of a local module morphism at a subopen. -/
abbrev app {U : X.Opens} (φ : Sections M N U) (V : Over U) :
    M.obj (op V.left) →ₗ[Γ(X, V.left)] Γ(N, V.left) := (φ.app (op V)).hom

@[ext]
lemma sections_ext {U : X.Opens} {φ ψ : Sections M N U}
    (h : ∀ V s, app M N φ V s = app M N ψ V s) : φ = ψ := by
  ext V s
  exact h V.unop s

/-- A local morphism commutes with restriction between any two subopens. -/
lemma app_naturality {U : X.Opens} (φ : Sections M N U) {V W : Over U}
    (i : W ⟶ V) (s : M.obj (op V.left)) :
    app M N φ W (M.presheaf.map i.left.op s) =
      N.presheaf.map i.left.op (app M N φ V s) :=
  PresheafOfModules.naturality_apply φ i.op s

/-- Scalars on an open act on every component by their restrictions. -/
def smul (U : X.Opens) (r : Γ(X, U)) (φ : Sections M N U) : Sections M N U :=
  PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        { toFun := fun s ↦ X.presheaf.map V.unop.hom.op r • app M N φ V.unop s
          map_zero' := by simp
          map_add' := by intros; simp [smul_add] }
      naturality := fun V W f ↦ by
        ext s
        have hn := PresheafOfModules.naturality_apply φ f s
        change app M N φ W.unop (M.presheaf.map f.unop.left.op s) =
          N.presheaf.map f.unop.left.op (app M N φ V.unop s) at hn
        change X.presheaf.map W.unop.hom.op r •
          app M N φ W.unop (M.presheaf.map f.unop.left.op s) =
            N.presheaf.map f.unop.left.op
              (X.presheaf.map V.unop.hom.op r • app M N φ V.unop s)
        rw [Scheme.Modules.map_smul, hn]
        congr 1
        exact congr($(X.presheaf.map_comp V.unop.hom.op f.unop.left.op) r) }
    (fun V a s ↦ by
      change Γ(X, V.unop.left) at a
      change X.presheaf.map V.unop.hom.op r • app M N φ V.unop (a • s) =
        a • (X.presheaf.map V.unop.hom.op r • app M N φ V.unop s)
      rw [map_smul]
      exact smul_comm _ _ _)

instance sectionsSMul (U : X.Opens) : SMul Γ(X, U) (Sections M N U) :=
  ⟨smul M N U⟩

@[simp]
lemma smul_app {U : X.Opens} (r : Γ(X, U)) (φ : Sections M N U)
    (V : Over U) (s : M.obj (op V.left)) :
    app M N (r • φ) V s = X.presheaf.map V.hom.op r • app M N φ V s := rfl

@[simp]
lemma add_app {U : X.Opens} (φ ψ : Sections M N U) (V : Over U)
    (s : M.obj (op V.left)) :
    app M N (φ + ψ) V s = app M N φ V s + app M N ψ V s := rfl

@[simp]
lemma zero_app {U : X.Opens} (V : Over U) (s : M.obj (op V.left)) :
    app M N (0 : Sections M N U) V s = 0 := rfl

instance sectionsModule (U : X.Opens) : Module Γ(X, U) (Sections M N U) where
  one_smul φ := by ext V s; simp
  mul_smul r t φ := by ext V s; simp [mul_smul]
  smul_zero r := by ext V s; simp
  smul_add r φ ψ := by ext V s; simp [smul_add]
  add_smul r t φ := by ext V s; simp [add_smul]
  zero_smul φ := by ext V s; simp

/-- Restriction of local morphisms is precomposition of their indexing category. -/
def restrict {U V : X.Opens} (i : V ⟶ U) (φ : Sections M N U) : Sections M N V :=
  PresheafOfModules.homMk
    (Functor.whiskerLeft (Over.map i).op ((PresheafOfModules.toPresheaf _).map φ))
    (fun W r s ↦ (app M N φ ((Over.map i).obj W.unop)).map_smul r s)

@[simp]
lemma restrict_app {U V : X.Opens} (i : V ⟶ U) (φ : Sections M N U)
    (W : Over V) (s : M.obj (op W.left)) :
    app M N (restrict M N i φ) W s = app M N φ ((Over.map i).obj W) s := rfl

@[simp]
lemma restrict_id (U : X.Opens) (φ : Sections M N U) :
    restrict M N (𝟙 U) φ = φ := by
  ext V s
  rfl

@[simp]
lemma restrict_comp {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V)
    (φ : Sections M N U) :
    restrict M N j (restrict M N i φ) = restrict M N (j ≫ i) φ := by
  ext Z s
  rfl

lemma restrict_smul {U V : X.Opens} (i : V ⟶ U)
    (r : Γ(X, U)) (φ : Sections M N U) :
    restrict M N i (r • φ) = X.presheaf.map i.op r • restrict M N i φ := by
  ext W s
  change X.presheaf.map (W.hom ≫ i).op r •
    (show Γ(N, W.left) from app M N φ ((Over.map i).obj W) s) =
    X.presheaf.map W.hom.op (X.presheaf.map i.op r) •
      (show Γ(N, W.left) from app M N φ ((Over.map i).obj W) s)
  rw [op_comp, Functor.map_comp]
  rfl

/-- The additive presheaf of local linear morphisms. -/
def addPresheaf : TopCat.Presheaf Ab X where
  obj U := AddCommGrpCat.of (Sections M N U.unop)
  map i := AddCommGrpCat.ofHom
    { toFun := restrict M N i.unop
      map_zero' := by ext V s; rfl
      map_add' := by intros; ext V s; rfl }
  map_id U := by ext φ : 2; exact restrict_id M N U.unop φ
  map_comp i j := by ext φ : 2; exact (restrict_comp M N i.unop j.unop φ).symm

instance addPresheafModule (U : X.Opensᵒᵖ) :
    Module (X.ringCatSheaf.obj.obj U) ((addPresheaf M N).obj U) :=
  sectionsModule M N U.unop

/-- The module-valued presheaf, with semilinear restriction. -/
def presheaf : X.PresheafOfModules :=
  PresheafOfModules.ofPresheaf (addPresheaf M N)
    (fun _ _ i r φ ↦ restrict_smul M N i.unop r φ)

/-- Evaluation of an additive local morphism. -/
abbrev addHomApp {U : X.Opens}
    (φ : (presheafHom M.presheaf N.presheaf).obj (op U)) (V : Over U) :
    M.obj (op V.left) →+ Γ(N, V.left) := (φ.app (op V)).hom

/-- The linear subfunctor of the additive internal Hom. -/
def linearHom : Subfunctor (presheafHom M.presheaf N.presheaf) where
  obj U := { φ | ∀ (V : Over U.unop) (r : Γ(X, V.left)) (s : M.obj (op V.left)),
    addHomApp M N φ V (r • s) = r • addHomApp M N φ V s }
  map i _ h V r s := h ((Over.map i.unop).obj V) r s

/-- Linearity descends along a covering sieve by separatedness of the target. -/
lemma linearHom_local (U : X.Opensᵒᵖ)
    (φ : (presheafHom M.presheaf N.presheaf).obj U)
    (hφ : (linearHom M N).sieveOfSection φ ∈ Opens.grothendieckTopology X U.unop) :
    φ ∈ (linearHom M N).obj U := by
  intro V r s
  have hN := (isSheaf_iff_isSheaf_of_type _ _).mp
    (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget Ab) N.isSheaf)
  apply (hN _ ((Opens.grothendieckTopology X).pullback_stable V.hom hφ)).isSeparatedFor.ext
  intro W g hg
  let f : Over.mk (g ≫ V.hom) ⟶ V := Over.homMk g
  have hn (t : M.obj (op V.left)) :
      addHomApp M N φ (Over.mk (g ≫ V.hom)) (M.presheaf.map g.op t) =
        N.presheaf.map g.op (addHomApp M N φ V t) := congr($(φ.naturality f.op) t)
  change N.presheaf.map g.op (addHomApp M N φ V (r • s)) =
    N.presheaf.map g.op (r • addHomApp M N φ V s)
  rw [Scheme.Modules.map_smul, ← hn, ← hn]
  change addHomApp M N φ (Over.mk (g ≫ V.hom)) (M.map g.op (r • s)) = _
  rw [M.map_smul]
  have hl := hg (Over.mk (𝟙 W)) (X.presheaf.map g.op r) (M.presheaf.map g.op s)
  have he := presheafHom_map_app_op_mk_id (F := M.presheaf)
    (G := N.presheaf) (g ≫ V.hom) φ
  dsimp only [addHomApp] at hl
  erw [he] at hl
  exact hl

/-- Compatible local linear maps glue uniquely. -/
lemma linearHom_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (linearHom M N).toFunctor := by
  rw [isSheaf_iff_isSheaf_of_type]
  apply (Subfunctor.isSheaf_iff _
    ((isSheaf_iff_isSheaf_of_type _ _).mp (N.isSheaf.hom M.presheaf))).mpr
  exact linearHom_local M N

/-- The linear predicate is precisely a module morphism on the slice. -/
def sectionsEquiv (U : X.Opens) : (linearHom M N).obj (op U) ≃ Sections M N U where
  toFun φ := PresheafOfModules.homMk φ.1 (fun V r s ↦ φ.2 V.unop r s)
  invFun φ := ⟨(PresheafOfModules.toPresheaf _).map φ,
    fun V r s ↦ (app M N φ V).map_smul r s⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The comparison commutes with restrictions. -/
def typesIso : (linearHom M N).toFunctor ≅ addPresheaf M N ⋙ forget Ab :=
  NatIso.ofComponents (fun U ↦ (sectionsEquiv M N U.unop).toIso) (fun _ ↦ rfl)

/-- The internal Hom presheaf is already a sheaf. -/
lemma presheaf_isSheaf :
    Presheaf.IsSheaf (Opens.grothendieckTopology X) (presheaf M N).presheaf := by
  apply Presheaf.isSheaf_of_isSheaf_comp _ _ (forget Ab)
  exact (Presheaf.isSheaf_of_iso_iff (typesIso M N)).mp (linearHom_isSheaf M N)

/-- The module sheaf of local linear morphisms into an arbitrary target. -/
def sheaf : X.Modules := ⟨presheaf M N, presheaf_isSheaf M N⟩

variable {M N}

/-- Contravariance in the source and covariance in the target. -/
def map {M' : X.PresheafOfModules} {N' : X.Modules} (f : M' ⟶ M) (g : N ⟶ N') :
    sheaf M N ⟶ sheaf M' N' :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := fun φ ↦
            (PresheafOfModules.pushforward₀ (Over.forget U.unop) _).map f ≫
              φ ≫ (g.over U.unop).val
          map_zero' := by simp
          map_add' := by
            intro φ ψ
            apply sections_ext
            intro V s
            change g.app V.left (app M N φ V (f.app (op V.left) s) +
              app M N ψ V (f.app (op V.left) s)) = _
            exact map_add (g.app V.left).hom _ _ }
      naturality := fun U V i ↦ by
        ext φ : 2
        apply sections_ext
        intro W s
        rfl }
    (fun U r φ ↦ by
      apply sections_ext
      intro W s
      change g.app W.left (X.presheaf.map W.hom.op r •
        app M N φ W (f.app (op W.left) s)) = _
      rw [Scheme.Modules.Hom.app_smul]
      rfl)⟩

@[simp]
lemma map_app {M' : X.PresheafOfModules} {N' : X.Modules} (f : M' ⟶ M) (g : N ⟶ N')
    (U : X.Opens) (φ : Sections M N U) (V : Over U) (s : M'.obj (op V.left)) :
    app M' N' ((map f g).app U φ) V s =
      g.app V.left (app M N φ V (f.app (op V.left) s)) := rfl

@[simp]
lemma map_id : map (𝟙 M) (𝟙 N) = 𝟙 (sheaf M N) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext φ : 2
  apply sections_ext
  intro V s
  rfl

@[reassoc]
lemma map_comp {M' M'' : X.PresheafOfModules} {N' N'' : X.Modules}
    (f : M' ⟶ M) (f' : M'' ⟶ M') (g : N ⟶ N') (g' : N' ⟶ N'') :
    map (f' ≫ f) (g ≫ g') = map f g ≫ map f' g' := by
  apply Scheme.Modules.hom_ext
  intro U
  ext φ : 2
  apply sections_ext
  intro V s
  rfl

end FLT.Mazur.FCurve.ModulePresheafLinearHom
