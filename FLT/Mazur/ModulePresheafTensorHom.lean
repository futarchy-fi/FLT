/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModulePresheafLinearHom
public import FLT.Mazur.ModuleSheafTensor

/-!
# Presheaf tensor, linear Hom, and sheafification units

Natural bilinear pairings on presheaves curry into the linear Hom sheaf.
The sheafification adjunction then proves that tensoring a sheafification
unit becomes invertible after sheafification.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite BraidedCategory

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

namespace FLT.Mazur.FCurve.ModulePresheafTensorHom

open ModulePresheafLinearHom (Sections sheaf app restrict sections_ext)
open PresheafOfModulesOfCommRing
open TensorProduct

variable {X : Scheme.{u}} {M N : X.PresheafOfModules} {P : X.Modules}

/-- Bilinear maps on every open, compatible with every restriction map. -/
structure Bilinear (M N : X.PresheafOfModules) (P : X.Modules) where
  /-- The bilinear map on sections of an open. -/
  app (U : X.Opens) : M.obj (op U) →ₗ[Γ(X, U)] N.obj (op U) →ₗ[Γ(X, U)] Γ(P, U)
  /-- Compatibility with restrictions. -/
  naturality {U V : X.Opens} (i : U ⟶ V) (m : M.obj (op V)) (n : N.obj (op V)) :
    app U (M.presheaf.map i.op m) (N.presheaf.map i.op n) =
      P.presheaf.map i.op (app V m n)

@[ext]
lemma Bilinear.ext {M N : X.PresheafOfModules} {P : X.Modules} {b c : Bilinear M N P}
    (h : ∀ U m n, b.app U m n = c.app U m n) : b = c := by
  have ha : b.app = c.app := by
    funext U
    ext m n
    exact h U m n
  cases b
  cases c
  cases ha
  rfl

/-- The sectionwise tensor universal property, with restriction compatibility. -/
def Bilinear.lift {M N : X.PresheafOfModules} {P : X.Modules} (b : Bilinear M N P) :
    Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val :=
  homMk (fun U ↦ ModuleCat.ofHom (TensorProduct.lift (b.app U.unop))) (fun f ↦ by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    exact b.naturality f.unop m n)

/-- A tensor-presheaf map determines a natural bilinear map. -/
def ofPresheafHom {M N : X.PresheafOfModules} {P : X.Modules}
    (f : Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val) :
    Bilinear M N P where
  app U := (TensorProduct.lift.equiv (RingHom.id Γ(X, U)) _ _ _).symm (f.app (.op U)).hom
  naturality i m n := PresheafOfModulesOfCommRing.naturality_apply f i.op (m ⊗ₜ n)

/-- Natural bilinear maps are precisely maps from the tensor presheaf. -/
def presheafHomEquiv (M N : X.PresheafOfModules) (P : X.Modules) :
    (Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val) ≃ Bilinear M N P where
  toFun := ofPresheafHom
  invFun := Bilinear.lift
  left_inv f := by
    ext1 U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl
  right_inv b := by
    ext U m n
    rfl

/-- Fixing the first section gives a linear map on every subopen. -/
def currySection (b : Bilinear M N P) (U : X.Opens) (m : M.obj (op U)) : Sections N P U :=
  PresheafOfModules.homMk
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
    (fun V r n ↦ (b.app V.unop.left (M.presheaf.map V.unop.hom.op m)).map_smul r n)

@[simp]
lemma currySection_app (b : Bilinear M N P) (U : X.Opens) (m : M.obj (op U))
    (V : Over U) (n : N.obj (op V.left)) :
    app N P (currySection b U m) V n =
      b.app V.left (M.presheaf.map V.hom.op m) n := rfl

/-- Currying a bilinear pairing as a morphism of module presheaves. -/
def curry (b : Bilinear M N P) : M ⟶ (sheaf N P).val :=
  PresheafOfModules.homMk
    { app U := AddCommGrpCat.ofHom
        { toFun := currySection b U.unop
          map_zero' := by
            apply sections_ext
            intro V n
            change b.app V.left (M.map V.hom.op 0) n = 0
            rw [map_zero, map_zero]
            rfl
          map_add' := by
            intro m m'
            apply sections_ext
            intro V n
            change b.app V.left (M.presheaf.map V.hom.op (m + m')) n =
              b.app V.left (M.presheaf.map V.hom.op m) n +
                b.app V.left (M.presheaf.map V.hom.op m') n
            change b.app V.left (M.map V.hom.op (m + m')) n = _
            rw [map_add, map_add]
            rfl }
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
      change b.app V.left (M.map V.hom.op (r • m)) n = _
      rw [M.map_smul]
      change b.app V.left (X.presheaf.map V.hom.op r • M.map V.hom.op m) n = _
      rw [map_smul, LinearMap.smul_apply]
      rfl)

@[simp]
lemma curry_app (b : Bilinear M N P) (U : X.Opens) (m : M.obj (op U))
    (V : Over U) (n : N.obj (op V.left)) :
    app N P ((curry b).app (op U) m) V n =
      b.app V.left (M.presheaf.map V.hom.op m) n := rfl

/-- Evaluate a local linear morphism on its whole domain. -/
def eval (U : X.Opens) (φ : Sections N P U) : N.obj (op U) →ₗ[Γ(X, U)] Γ(P, U) :=
  app N P φ (Over.mk (𝟙 U))

@[simp]
lemma eval_smul (U : X.Opens) (r : Γ(X, U)) (φ : Sections N P U) (n : N.obj (op U)) :
    eval U (r • φ) n = r • eval U φ n := by
  change X.presheaf.map (𝟙 U).op r • eval U φ n = r • eval U φ n
  simp

/-- Evaluation commutes with restriction of both the morphism and its argument. -/
lemma eval_restrict {U V : X.Opens} (i : V ⟶ U) (φ : Sections N P U) (n : N.obj (op U)) :
    eval V (restrict N P i φ) (N.presheaf.map i.op n) =
      P.presheaf.map i.op (eval U φ n) :=
  ModulePresheafLinearHom.app_naturality N P φ
    (Over.homMk i : Over.mk (𝟙 V ≫ i) ⟶ Over.mk (𝟙 U)) n

/-- Uncurrying is the natural bilinear pairing given by evaluation. -/
def uncurry (f : M ⟶ (sheaf N P).val) : Bilinear M N P where
  app U :=
    { toFun := fun m ↦ eval U (f.app (op U) m)
      map_add' := by
        intro m m'
        ext n
        simp only [map_add]
        rfl
      map_smul' := by
        intro r m
        ext n
        rw [(f.app (op U)).hom.map_smul, eval_smul]
        rfl }
  naturality i m n := by
    change eval _ (f.app (op _) (M.presheaf.map i.op m)) (N.presheaf.map i.op n) = _
    have hf := congr($(((PresheafOfModules.toPresheaf _).map f).naturality i.op) m)
    change f.app (op _) (M.presheaf.map i.op m) = restrict N P i (f.app (op _) m) at hf
    rw [hf, eval_restrict]
    rfl

@[simp]
lemma uncurry_app (f : M ⟶ (sheaf N P).val) (U : X.Opens) (m : M.obj (op U)) (n : N.obj (op U)) :
    (uncurry f).app U m n = eval U (f.app (op U) m) n := rfl

@[simp]
lemma uncurry_curry (b : Bilinear M N P) : uncurry (curry b) = b := by
  ext U m n
  change b.app U (M.presheaf.map (𝟙 U).op m) n = b.app U m n
  simp

@[simp]
lemma curry_uncurry (f : M ⟶ (sheaf N P).val) : curry (uncurry f) = f := by
  ext1 U
  obtain ⟨U⟩ := U
  ext m : 2
  apply sections_ext
  intro V n
  rw [curry_app, uncurry_app]
  have hf := congr($(((PresheafOfModules.toPresheaf _).map f).naturality V.hom.op) m)
  change f.app (op V.left) (M.presheaf.map V.hom.op m) =
    restrict N P V.hom (f.app (op U) m) at hf
  rw [hf]
  rfl

/-- Natural bilinear pairings correspond to maps into the internal Hom sheaf. -/
def bilinearEquiv (M N : X.PresheafOfModules) (P : X.Modules) :
    Bilinear M N P ≃ (M ⟶ (sheaf N P).val) where
  toFun := curry
  invFun := uncurry
  left_inv := uncurry_curry
  right_inv := curry_uncurry

/-- Currying for maps from the sectionwise tensor into any module sheaf. -/
def homEquiv (M N : X.PresheafOfModules) (P : X.Modules) :
    (Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val) ≃
      (M ⟶ (sheaf N P).val) :=
  (presheafHomEquiv M N P).trans (bilinearEquiv M N P)

/-- The equivalent convention that curries the second tensor variable. -/
def homEquivRight (M N : X.PresheafOfModules) (P : X.Modules) :
    (Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val) ≃
      (N ⟶ (sheaf M P).val) :=
  (Iso.homCongr (braiding (C := PresheafOfModulesOfCommRing X.presheaf) M N)
    (Iso.refl P.val)).trans (homEquiv N M P)

/-- Right currying restricts the second section to each subopen. -/
lemma homEquivRight_app (k : Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val)
    (U : X.Opens) (n : N.obj (op U)) (V : Over U) (m : M.obj (op V.left)) :
    app M P ((homEquivRight M N P k).app (op U) n) V m =
      k.app (op V.left) (m ⊗ₜ[Γ(X, V.left)] N.map V.hom.op n) := rfl

/-- Currying evaluates by restricting the first input and then taking a pure tensor. -/
lemma homEquiv_app (k : Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val)
    (U : X.Opens) (m : M.obj (op U)) (V : Over U) (n : N.obj (op V.left)) :
    app N P ((homEquiv M N P k).app (op U) m) V n =
      k.app (op V.left) (M.map V.hom.op m ⊗ₜ[Γ(X, V.left)] n) := rfl

/-- Uncurrying evaluates pure tensors on the identity subopen. -/
lemma homEquiv_symm_tmul (k : M ⟶ (sheaf N P).val) (U : X.Opens)
    (m : M.obj (op U)) (n : N.obj (op U)) :
    ((homEquiv M N P).symm k).app (op U) (m ⊗ₜ[Γ(X, U)] n) =
      eval U (k.app (op U) m) n := rfl

/-- The tensor/Hom correspondence is natural in all three variables. -/
lemma homEquiv_natural {M' N' : X.PresheafOfModules} {P' : X.Modules}
    (f : M' ⟶ M) (g : N' ⟶ N) (h : P ⟶ P')
    (k : Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val) :
    homEquiv M' N' P' (Monoidal.tensorHom f g ≫ k ≫ h.val) =
      f ≫ homEquiv M N P k ≫ (ModulePresheafLinearHom.map g h).val := by
  ext1 U
  ext m : 2
  apply sections_ext
  intro V n
  change h.app V.left (k.app (op V.left)
    (f.app (op V.left) (M'.map V.hom.op m) ⊗ₜ g.app (op V.left) n)) =
      h.app V.left (k.app (op V.left)
        (M.map V.hom.op (f.app U m) ⊗ₜ g.app (op V.left) n))
  rw [PresheafOfModules.naturality_apply]

/-- Naturality in the first input alone. -/
lemma homEquiv_precomp {M' : X.PresheafOfModules} (f : M' ⟶ M)
    (k : Monoidal.tensorObj (R := X.presheaf) M N ⟶ P.val) :
    homEquiv M' N P (Monoidal.tensorHom f (𝟙 N) ≫ k) = f ≫ homEquiv M N P k := by
  have h := homEquiv_natural f (𝟙 N) (𝟙 P) k
  rw [ModulePresheafLinearHom.map_id] at h
  change homEquiv M' N P (Monoidal.tensorHom f (𝟙 N) ≫ k ≫ 𝟙 _) =
    f ≫ homEquiv M N P k ≫ 𝟙 _ at h
  simpa using h

/-- The tensor/Hom equivalence after sheafifying its tensor source. -/
def sheafHomEquiv (M N : X.PresheafOfModules) (P : X.Modules) :
    ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj
      (Monoidal.tensorObj (R := X.presheaf) M N) ⟶ P) ≃ (M ⟶ (sheaf N P).val) :=
  ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).homEquiv _ _).trans
    (homEquiv M N P)

/-- Tensoring a sheafification unit in the first variable is inverted by sheafification. -/
theorem isIso_tensor_unit_left (M N : X.PresheafOfModules) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (Monoidal.tensorHom
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app M)
        (𝟙 N))) := by
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  apply isIso_of_coyoneda_map_bijective
  intro P
  let e := (sheafHomEquiv (S.obj M).val N P).trans
    (((SheafOfModules.fullyFaithfulForget X.ringCatSheaf).homEquiv).symm.trans
      ((adj.homEquiv M (sheaf N P)).trans (sheafHomEquiv M N P).symm))
  change Function.Bijective (fun k : S.obj
    (Monoidal.tensorObj (R := X.presheaf) (S.obj M).val N) ⟶ P ↦
      S.map (Monoidal.tensorHom (show M ⟶ (S.obj M).val from adj.unit.app M) (𝟙 N)) ≫ k)
  convert e.bijective using 1
  funext k
  apply (sheafHomEquiv M N P).injective
  change homEquiv M N P (adj.homEquiv _ _ (S.map _ ≫ k)) = _
  rw [adj.homEquiv_naturality_left, homEquiv_precomp]
  dsimp only [e, Equiv.trans_apply]
  erw [Equiv.apply_symm_apply]
  rfl

/-- Symmetry gives the same result for the second tensor variable. -/
theorem isIso_tensor_unit_right (M N : X.PresheafOfModules) :
    IsIso ((PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).map
      (Monoidal.tensorHom (𝟙 M)
        ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app N))) := by
  let S := PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)
  let η (A : X.PresheafOfModules) : A ⟶ (S.obj A).val :=
    (PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app A
  let := isIso_tensor_unit_left N M
  change IsIso (S.map (Monoidal.tensorHom (𝟙 M) (η N)))
  have he : Monoidal.tensorHom (𝟙 M) (η N) =
      (braiding (C := PresheafOfModulesOfCommRing X.presheaf) M N).hom ≫
        Monoidal.tensorHom (η N) (𝟙 M) ≫
          (braiding (C := PresheafOfModulesOfCommRing X.presheaf) (S.obj N).val M).hom := by
    ext1 U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro m n
    rfl
  rw [he, S.map_comp, S.map_comp]
  infer_instance

end FLT.Mazur.FCurve.ModulePresheafTensorHom
