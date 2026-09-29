/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafInternalHom
public import FLT.Mazur.ModuleSheafTensor

/-!
# Currying for the concrete sheaf tensor

A natural bilinear pairing gives a map into internal Hom by restricting the
first section to every subopen. Evaluation at the identity subopen is inverse.
Composing with the sheafified tensor's universal property gives a closed
adjunction, with no generation assumption on global tensor sections.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve.ModuleSheafTensorCurrying

open ModuleSheafInternalHom (Sections sheaf app restrict sections_ext)
open ModuleSheafTensor (Bilinear tensor pure)

variable {X : Scheme.{u}} {M N P : X.Modules}

/-- Fixing the first section gives a linear map on every subopen. -/
def currySection (b : Bilinear M N P) (U : X.Opens) (m : Γ(M, U)) : Sections N P U :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        (b.app V.unop.left (M.presheaf.map V.unop.hom.op m)).toAddMonoidHom
      naturality := fun V W i ↦ by
        ext n
        change b.app W.unop.left (M.presheaf.map W.unop.hom.op m)
          (N.presheaf.map i.unop.left.op n) =
            P.presheaf.map i.unop.left.op
              (b.app V.unop.left (M.presheaf.map V.unop.hom.op m) n)
        rw [← b.naturality]
        congr 2
        exact congr($(M.presheaf.map_comp V.unop.hom.op i.unop.left.op) m) }
    (fun V r n ↦ (b.app V.unop.left (M.presheaf.map V.unop.hom.op m)).map_smul r n)⟩

@[simp]
lemma currySection_app (b : Bilinear M N P) (U : X.Opens) (m : Γ(M, U))
    (V : Over U) (n : Γ(N, V.left)) :
    app N P (currySection b U m) V n =
      b.app V.left (M.presheaf.map V.hom.op m) n := rfl

/-- Currying a bilinear pairing as a morphism of module sheaves. -/
def curry (b : Bilinear M N P) : M ⟶ sheaf N P :=
  ⟨PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := currySection b U.unop
          map_zero' := by
            apply sections_ext
            intro V n
            simp
          map_add' := by
            intro m m'
            apply sections_ext
            intro V n
            change b.app V.left (M.presheaf.map V.hom.op (m + m')) n =
              b.app V.left (M.presheaf.map V.hom.op m) n +
                b.app V.left (M.presheaf.map V.hom.op m') n
            simp }
      naturality := fun U V i ↦ by
        ext m : 2
        apply sections_ext
        intro W n
        change b.app W.left (M.presheaf.map W.hom.op (M.presheaf.map i m)) n =
          b.app W.left (M.presheaf.map (W.hom ≫ i.unop).op m) n
        rw [op_comp, Functor.map_comp]
        rfl }
    (fun U r m ↦ by
      change Γ(X, U.unop) at r
      apply sections_ext
      intro V n
      change b.app V.left (M.presheaf.map V.hom.op (r • m)) n =
        X.presheaf.map V.hom.op r • b.app V.left (M.presheaf.map V.hom.op m) n
      rw [Scheme.Modules.map_smul, map_smul, LinearMap.smul_apply])⟩

@[simp]
lemma curry_app (b : Bilinear M N P) (U : X.Opens) (m : Γ(M, U))
    (V : Over U) (n : Γ(N, V.left)) :
    app N P ((curry b).app U m) V n =
      b.app V.left (M.presheaf.map V.hom.op m) n := rfl

/-- Evaluate a local linear morphism on its whole domain. -/
def eval (U : X.Opens) (φ : Sections N P U) : Γ(N, U) →ₗ[Γ(X, U)] Γ(P, U) :=
  app N P φ (Over.mk (𝟙 U))

@[simp]
lemma eval_smul (U : X.Opens) (r : Γ(X, U)) (φ : Sections N P U) (n : Γ(N, U)) :
    eval U (r • φ) n = r • eval U φ n := by
  change X.presheaf.map (𝟙 U).op r • eval U φ n = r • eval U φ n
  simp

/-- Evaluation commutes with restriction of both the morphism and its argument. -/
lemma eval_restrict {U V : X.Opens} (i : V ⟶ U) (φ : Sections N P U) (n : Γ(N, U)) :
    eval V (restrict N P i φ) (N.presheaf.map i.op n) =
      P.presheaf.map i.op (eval U φ n) :=
  ModuleSheafInternalHom.app_naturality N P φ
    (Over.homMk i : Over.mk (𝟙 V ≫ i) ⟶ Over.mk (𝟙 U)) n

/-- Uncurrying is the natural bilinear pairing given by evaluation. -/
def uncurry (f : M ⟶ sheaf N P) : Bilinear M N P where
  app U :=
    { toFun := fun m ↦ eval U (f.app U m)
      map_add' := by
        intro m m'
        ext n
        simp only [map_add]
        rfl
      map_smul' := by
        intro r m
        ext n
        rw [Scheme.Modules.Hom.app_smul, eval_smul]
        rfl }
  naturality i m n := by
    change eval _ (f.app _ (M.presheaf.map i.op m)) (N.presheaf.map i.op n) = _
    have hf := congr($(f.mapPresheaf.naturality i.op) m)
    change f.app _ (M.presheaf.map i.op m) = restrict N P i (f.app _ m) at hf
    rw [hf, eval_restrict]
    rfl

@[simp]
lemma uncurry_app (f : M ⟶ sheaf N P) (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (uncurry f).app U m n = eval U (f.app U m) n := rfl

@[simp]
lemma uncurry_curry (b : Bilinear M N P) : uncurry (curry b) = b := by
  ext U m n
  change b.app U (M.presheaf.map (𝟙 U).op m) n = b.app U m n
  simp

@[simp]
lemma curry_uncurry (f : M ⟶ sheaf N P) : curry (uncurry f) = f := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m : 2
  apply sections_ext
  intro V n
  rw [curry_app, uncurry_app]
  have hf := congr($(f.mapPresheaf.naturality V.hom.op) m)
  change f.app V.left (M.presheaf.map V.hom.op m) =
    restrict N P V.hom (f.app U m) at hf
  rw [hf]
  rfl

/-- Natural bilinear pairings correspond to maps into the internal Hom sheaf. -/
def bilinearEquiv (M N P : X.Modules) : Bilinear M N P ≃ (M ⟶ sheaf N P) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/-- The closed Hom equivalence for the concrete sheafified tensor. -/
def homEquiv (M N P : X.Modules) : (tensor M N ⟶ P) ≃ (M ⟶ sheaf N P) :=
  (ModuleSheafTensor.homEquiv M N P).trans (bilinearEquiv M N P)

/-- Curried evaluation on a subopen is evaluation on a pure tensor there. -/
lemma homEquiv_app (f : tensor M N ⟶ P) (U : X.Opens) (m : Γ(M, U))
    (V : Over U) (n : Γ(N, V.left)) :
    app N P ((homEquiv M N P f).app U m) V n =
      f.app V.left (pure M N V.left (M.presheaf.map V.hom.op m) n) := rfl

/-- The inverse closed equivalence has the expected pure-section evaluation law. -/
@[simp]
lemma homEquiv_symm_pure (f : M ⟶ sheaf N P) (U : X.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) :
    ((homEquiv M N P).symm f).app U (pure M N U m n) = eval U (f.app U m) n :=
  ModuleSheafTensor.lift_pure (uncurry f) U m n

/-- The bilinear correspondence is natural in both inputs and the output. -/
lemma uncurry_natural {M' N' P' : X.Modules} (f : M' ⟶ M) (g : N' ⟶ N)
    (h : P ⟶ P') (k : M ⟶ sheaf N P) (U : X.Opens)
    (m : Γ(M', U)) (n : Γ(N', U)) :
    (uncurry (f ≫ k ≫ ModuleSheafInternalHom.map g h)).app U m n =
      h.app U ((uncurry k).app U (f.app U m) (g.app U n)) := rfl

/-- Naturality of the closed equivalence in all three module sheaves. -/
lemma homEquiv_natural {M' N' P' : X.Modules} (f : M' ⟶ M) (g : N' ⟶ N)
    (h : P ⟶ P') (k : tensor M N ⟶ P) :
    homEquiv M' N' P' (ModuleSheafTensor.map f g ≫ k ≫ h) =
      f ≫ homEquiv M N P k ≫ ModuleSheafInternalHom.map g h := by
  apply Scheme.Modules.hom_ext
  intro U
  ext m : 2
  apply sections_ext
  intro V n
  change (ModuleSheafTensor.map f g ≫ k ≫ h).app V.left
    (pure M' N' V.left (M'.presheaf.map V.hom.op m) n) =
      h.app V.left (k.app V.left
        (pure M N V.left (M.presheaf.map V.hom.op (f.app U m)) (g.app V.left n)))
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ModuleSheafTensor.map_pure]
  have hf := congr($(f.mapPresheaf.naturality V.hom.op) m)
  change f.app V.left (M'.presheaf.map V.hom.op m) =
    M.presheaf.map V.hom.op (f.app U m) at hf
  rw [hf]

/-- Naturality in the target, for use in the adjunction constructor. -/
lemma homEquiv_postcomp {P' : X.Modules} (k : tensor M N ⟶ P) (h : P ⟶ P') :
    homEquiv M N P' (k ≫ h) =
      homEquiv M N P k ≫ ModuleSheafInternalHom.map (𝟙 N) h := by
  simpa using homEquiv_natural (𝟙 M) (𝟙 N) h k

/-- Uncurrying commutes with precomposition in the first variable. -/
lemma homEquiv_symm_precomp {M' : X.Modules} (f : M' ⟶ M) (k : M ⟶ sheaf N P) :
    (homEquiv M' N P).symm (f ≫ k) =
      ModuleSheafTensor.map f (𝟙 N) ≫ (homEquiv M N P).symm k := by
  apply ModuleSheafTensor.hom_ext
  intro U m n
  simp only [homEquiv_symm_pure, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, ModuleSheafTensor.map_pure, Scheme.Modules.Hom.id_app,
    ConcreteCategory.id_apply]

/-- Tensoring on the right by a fixed module sheaf. -/
def tensoring (N : X.Modules) : X.Modules ⥤ X.Modules where
  obj M := tensor M N
  map f := ModuleSheafTensor.map f (𝟙 N)
  map_id M := ModuleSheafTensor.map_id M N
  map_comp f g := by simpa using ModuleSheafTensor.map_comp f g (𝟙 N) (𝟙 N)

/-- Internal Hom from a fixed module sheaf, as a covariant functor. -/
def homFunctor (N : X.Modules) : X.Modules ⥤ X.Modules where
  obj P := sheaf N P
  map h := ModuleSheafInternalHom.map (𝟙 N) h
  map_id P := ModuleSheafInternalHom.map_id
  map_comp h k := by simpa using ModuleSheafInternalHom.map_comp (𝟙 N) (𝟙 N) h k

/-- The concrete sheafified tensor is left adjoint to internal Hom. -/
def adjunction (N : X.Modules) : tensoring N ⊣ homFunctor N :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun M P ↦ homEquiv M N P
      homEquiv_naturality_left_symm := homEquiv_symm_precomp
      homEquiv_naturality_right := homEquiv_postcomp }

/-- Evaluation is the counit of the concrete closed correspondence. -/
def evaluation (N P : X.Modules) : tensor (sheaf N P) N ⟶ P :=
  (homEquiv (sheaf N P) N P).symm (𝟙 _)

@[simp]
lemma evaluation_pure (U : X.Opens) (φ : Sections N P U) (n : Γ(N, U)) :
    (evaluation N P).app U (pure (sheaf N P) N U φ n) = eval U φ n :=
  homEquiv_symm_pure (𝟙 _) U φ n

/-- Every tensor morphism factors through evaluation of its curried morphism. -/
lemma curry_evaluation (k : tensor M N ⟶ P) :
    ModuleSheafTensor.map (homEquiv M N P k) (𝟙 N) ≫ evaluation N P = k := by
  rw [evaluation, ← homEquiv_symm_precomp, Category.comp_id, Equiv.symm_apply_apply]

end FLT.Mazur.FCurve.ModuleSheafTensorCurrying
