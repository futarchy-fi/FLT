/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafTensorCurrying

/-!
# Associativity of the sheaf tensor

Restriction-compatible trilinear maps extend by currying into internal Hom.
Nested local pure sections determine the extension, even when global pure
sections do not generate all sections of either tensor sheaf.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve.ModuleSheafTensorAssociator

open ModuleSheafTensor (tensor pure Bilinear)
open ModuleSheafInternalHom (Sections sheaf app sections_ext)
open ModuleSheafTensorCurrying (eval)

variable {X : Scheme.{u}} {M N K P : X.Modules}

/-- A trilinear pairing on sections, compatible with restriction. -/
structure Trilinear (M N K P : X.Modules) where
  /-- The trilinear map on each open. -/
  app (U : X.Opens) :
    Γ(M, U) →ₗ[Γ(X, U)] Γ(N, U) →ₗ[Γ(X, U)] Γ(K, U) →ₗ[Γ(X, U)] Γ(P, U)
  /-- Restricting all three arguments restricts the result. -/
  naturality {U V : X.Opens} (i : U ⟶ V)
      (m : Γ(M, V)) (n : Γ(N, V)) (k : Γ(K, V)) :
    app U (M.presheaf.map i.op m) (N.presheaf.map i.op n) (K.presheaf.map i.op k) =
      P.presheaf.map i.op (app V m n k)

/-- Curry the third argument on every subopen. -/
def Trilinear.section (b : Trilinear M N K P) (U : X.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) : Sections K P U :=
  ⟨PresheafOfModules.homMk
    { app V := AddCommGrpCat.ofHom
        (b.app V.unop.left (M.presheaf.map V.unop.hom.op m)
          (N.presheaf.map V.unop.hom.op n)).toAddMonoidHom
      naturality := fun V W i ↦ by
        ext k
        change b.app W.unop.left (M.presheaf.map W.unop.hom.op m)
          (N.presheaf.map W.unop.hom.op n) (K.presheaf.map i.unop.left.op k) =
            P.presheaf.map i.unop.left.op (b.app V.unop.left
              (M.presheaf.map V.unop.hom.op m) (N.presheaf.map V.unop.hom.op n) k)
        rw [← b.naturality]
        have hm : M.presheaf.map W.unop.hom.op m =
            M.presheaf.map i.unop.left.op (M.presheaf.map V.unop.hom.op m) :=
          congr($(M.presheaf.map_comp V.unop.hom.op i.unop.left.op) m)
        have hn : N.presheaf.map W.unop.hom.op n =
            N.presheaf.map i.unop.left.op (N.presheaf.map V.unop.hom.op n) :=
          congr($(N.presheaf.map_comp V.unop.hom.op i.unop.left.op) n)
        rw [hm, hn] }
    (fun V r k ↦ (b.app V.unop.left _ _).map_smul r k)⟩

@[simp]
lemma Trilinear.section_app (b : Trilinear M N K P) (U : X.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) (V : Over U) (k : Γ(K, V.left)) :
    ModuleSheafInternalHom.app K P (b.section U m n) V k =
      b.app V.left (M.presheaf.map V.hom.op m) (N.presheaf.map V.hom.op n) k := rfl

/-- The curried trilinear pairing is bilinear with values in internal Hom. -/
def Trilinear.curry (b : Trilinear M N K P) : Bilinear M N (sheaf K P) where
  app U :=
    { toFun := fun m ↦
        { toFun := b.section U m
          map_add' := by
            intro n n'
            apply sections_ext
            intro V k
            change b.app V.left (M.presheaf.map V.hom.op m)
              (N.presheaf.map V.hom.op (n + n')) k =
                b.app V.left (M.presheaf.map V.hom.op m)
                  (N.presheaf.map V.hom.op n) k +
                b.app V.left (M.presheaf.map V.hom.op m)
                  (N.presheaf.map V.hom.op n') k
            simp
          map_smul' := by
            intro r n
            apply sections_ext
            intro V k
            change b.app V.left (M.presheaf.map V.hom.op m)
              (N.presheaf.map V.hom.op (r • n)) k =
                X.presheaf.map V.hom.op r • b.app V.left
                  (M.presheaf.map V.hom.op m) (N.presheaf.map V.hom.op n) k
            simp [Scheme.Modules.map_smul] }
      map_add' := by
        intro m m'
        ext n : 1
        apply sections_ext
        intro V k
        change b.app V.left (M.presheaf.map V.hom.op (m + m'))
          (N.presheaf.map V.hom.op n) k =
            b.app V.left (M.presheaf.map V.hom.op m) (N.presheaf.map V.hom.op n) k +
            b.app V.left (M.presheaf.map V.hom.op m') (N.presheaf.map V.hom.op n) k
        simp
      map_smul' := by
        intro r m
        ext n : 1
        apply sections_ext
        intro V k
        change b.app V.left (M.presheaf.map V.hom.op (r • m))
          (N.presheaf.map V.hom.op n) k = X.presheaf.map V.hom.op r •
            b.app V.left (M.presheaf.map V.hom.op m) (N.presheaf.map V.hom.op n) k
        simp [Scheme.Modules.map_smul] }
  naturality i m n := by
    apply sections_ext
    intro V k
    change b.app V.left (M.presheaf.map V.hom.op (M.presheaf.map i.op m))
      (N.presheaf.map V.hom.op (N.presheaf.map i.op n)) k =
        b.app V.left (M.presheaf.map (V.hom ≫ i).op m)
          (N.presheaf.map (V.hom ≫ i).op n) k
    rw [op_comp, Functor.map_comp, Functor.map_comp]
    rfl

/-- Extend a trilinear pairing to the left-associated tensor by closedness. -/
def Trilinear.lift (b : Trilinear M N K P) : tensor (tensor M N) K ⟶ P :=
  (ModuleSheafTensorCurrying.homEquiv _ _ _).symm (ModuleSheafTensor.lift b.curry)

@[simp]
lemma Trilinear.lift_pure (b : Trilinear M N K P) (U : X.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) (k : Γ(K, U)) :
    b.lift.app U (pure (tensor M N) K U (pure M N U m n) k) = b.app U m n k := by
  rw [Trilinear.lift, ModuleSheafTensorCurrying.homEquiv_symm_pure,
    ModuleSheafTensor.lift_pure]
  change b.app U (M.presheaf.map (𝟙 U).op m) (N.presheaf.map (𝟙 U).op n) k = _
  simp

/-- Nested pure sections on all opens determine maps from a left-associated tensor. -/
lemma left_hom_ext {f g : tensor (tensor M N) K ⟶ P}
    (h : ∀ U m n k, f.app U (pure (tensor M N) K U (pure M N U m n) k) =
      g.app U (pure (tensor M N) K U (pure M N U m n) k)) : f = g := by
  apply (ModuleSheafTensorCurrying.homEquiv _ _ _).injective
  apply ModuleSheafTensor.hom_ext
  intro U m n
  apply sections_ext
  intro V k
  change f.app V.left (pure (tensor M N) K V.left
    ((tensor M N).presheaf.map V.hom.op (pure M N U m n)) k) =
      g.app V.left (pure (tensor M N) K V.left
        ((tensor M N).presheaf.map V.hom.op (pure M N U m n)) k)
  rw [ModuleSheafTensor.pure_restrict]
  exact h _ _ _ _

/-- Symmetry of the concrete tensor, constructed from the flipped pairing. -/
def comm (M N : X.Modules) : tensor M N ≅ tensor N M where
  hom := ModuleSheafTensor.lift
    { app U := ((ModuleSheafTensor.pairing N M).app U).flip
      naturality i m n := (ModuleSheafTensor.pairing N M).naturality i n m }
  inv := ModuleSheafTensor.lift
    { app U := ((ModuleSheafTensor.pairing M N).app U).flip
      naturality i n m := (ModuleSheafTensor.pairing M N).naturality i m n }
  hom_inv_id := by
    apply ModuleSheafTensor.hom_ext
    intro U m n
    simp
  inv_hom_id := by
    apply ModuleSheafTensor.hom_ext
    intro U n m
    simp

@[simp]
lemma comm_hom_pure (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) :
    (comm M N).hom.app U (pure M N U m n) = pure N M U n m :=
  ModuleSheafTensor.lift_pure _ U m n

/-- Nested pure sections also determine maps from a right-associated tensor. -/
lemma right_hom_ext {f g : tensor M (tensor N K) ⟶ P}
    (h : ∀ U m n k, f.app U (pure M (tensor N K) U m (pure N K U n k)) =
      g.app U (pure M (tensor N K) U m (pure N K U n k))) : f = g := by
  apply (cancel_epi (comm (tensor N K) M).hom).mp
  apply left_hom_ext
  intro U n k m
  simpa using h U m n k

/-- The right-associated pure tensor is a natural trilinear pairing. -/
def rightPairing (M N K : X.Modules) : Trilinear M N K (tensor M (tensor N K)) where
  app U :=
    { toFun := fun m ↦ ((ModuleSheafTensor.pairing N K).app U).compr₂
        ((ModuleSheafTensor.pairing M (tensor N K)).app U m)
      map_add' := by intros; ext n k; simp
      map_smul' := by intros; ext n k; simp }
  naturality i m n k := by
    change pure M (tensor N K) _ (M.presheaf.map i.op m)
      (pure N K _ (N.presheaf.map i.op n) (K.presheaf.map i.op k)) =
        (tensor M (tensor N K)).presheaf.map i.op (pure M (tensor N K) _ m
          (pure N K _ n k))
    simp only [ModuleSheafTensor.pure_restrict]

/-- Rotate the inputs of the left-associated pure tensor. -/
def rotatedPairing (M N K : X.Modules) : Trilinear N K M (tensor (tensor M N) K) where
  app U :=
    { toFun := fun n ↦
        { toFun := fun k ↦ (((ModuleSheafTensor.pairing (tensor M N) K).app U).flip k).comp
            (((ModuleSheafTensor.pairing M N).app U).flip n)
          map_add' := by intros; ext m; simp
          map_smul' := by intros; ext m; simp }
      map_add' := by intros; ext k m; simp
      map_smul' := by intros; ext k m; simp }
  naturality i n k m := by
    change pure (tensor M N) K _
      (pure M N _ (M.presheaf.map i.op m) (N.presheaf.map i.op n))
      (K.presheaf.map i.op k) = (tensor (tensor M N) K).presheaf.map i.op
        (pure (tensor M N) K _ (pure M N _ m n) k)
    simp only [ModuleSheafTensor.pure_restrict]

/-- The forward associativity morphism. -/
def forward (M N K : X.Modules) : tensor (tensor M N) K ⟶ tensor M (tensor N K) :=
  (rightPairing M N K).lift

/-- The reverse associativity morphism. -/
def backward (M N K : X.Modules) : tensor M (tensor N K) ⟶ tensor (tensor M N) K :=
  (comm M (tensor N K)).hom ≫ (rotatedPairing M N K).lift

@[simp]
lemma forward_pure (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (k : Γ(K, U)) :
    (forward M N K).app U (pure (tensor M N) K U (pure M N U m n) k) =
      pure M (tensor N K) U m (pure N K U n k) :=
  Trilinear.lift_pure _ U m n k

@[simp]
lemma backward_pure (U : X.Opens) (m : Γ(M, U)) (n : Γ(N, U)) (k : Γ(K, U)) :
    (backward M N K).app U (pure M (tensor N K) U m (pure N K U n k)) =
      pure (tensor M N) K U (pure M N U m n) k := by
  simp only [backward, Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    comm_hom_pure, Trilinear.lift_pure]
  rfl

/-- The associator of the actual sheafified tensor. -/
def associator (M N K : X.Modules) : tensor (tensor M N) K ≅ tensor M (tensor N K) where
  hom := forward M N K
  inv := backward M N K
  hom_inv_id := by
    apply left_hom_ext
    intro U m n k
    simp
  inv_hom_id := by
    apply right_hom_ext
    intro U m n k
    simp

/-- The associator sends a nested pure section to its other parenthesization. -/
@[simp]
lemma associator_hom_pure (U : X.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) (k : Γ(K, U)) :
    (associator M N K).hom.app U (pure (tensor M N) K U (pure M N U m n) k) =
      pure M (tensor N K) U m (pure N K U n k) := forward_pure U m n k

/-- The inverse associator has the reverse nested pure-section formula. -/
@[simp]
lemma associator_inv_pure (U : X.Opens)
    (m : Γ(M, U)) (n : Γ(N, U)) (k : Γ(K, U)) :
    (associator M N K).inv.app U (pure M (tensor N K) U m (pure N K U n k)) =
      pure (tensor M N) K U (pure M N U m n) k := backward_pure U m n k

/-- Naturality in all three module sheaves. -/
@[reassoc]
lemma associator_naturality {M' N' K' : X.Modules}
    (f : M ⟶ M') (g : N ⟶ N') (h : K ⟶ K') :
    ModuleSheafTensor.map (ModuleSheafTensor.map f g) h ≫ (associator M' N' K').hom =
      (associator M N K).hom ≫ ModuleSheafTensor.map f (ModuleSheafTensor.map g h) := by
  apply left_hom_ext
  intro U m n k
  simp [associator]

end FLT.Mazur.FCurve.ModuleSheafTensorAssociator
