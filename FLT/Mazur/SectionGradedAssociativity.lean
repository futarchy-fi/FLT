/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedUnit

/-!
# Associativity on arbitrary tensor-power sections

Extensionality for sheaf morphisms reduces the recursive proof to local
pure tensors. No spanning assertion about sections on a fixed open is used.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedMultiplication
open FCurve ModuleLineBundleTensorPullback ModuleSheafTensor
open ModuleSheafTensorAssociator
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false
variable {X : Scheme.{u}} (L : X.Modules)

/-- Four local tensor factors determine a morphism from the left-associated tensor. -/
lemma four_hom_ext {A B C D P : X.Modules}
    {f g : tensor (tensor (tensor A B) C) D ⟶ P}
    (h : ∀ U a b c d, f.app U (pure _ _ U (pure _ _ U (pure _ _ U a b) c) d) =
      g.app U (pure _ _ U (pure _ _ U (pure _ _ U a b) c) d)) : f = g := by
  apply (ModuleSheafTensorCurrying.homEquiv _ _ _).injective
  apply left_hom_ext
  intro U a b c
  apply ModuleSheafInternalHom.sections_ext
  intro V d
  change f.app V.left (pure _ _ V.left
    ((tensor (tensor A B) C).presheaf.map V.hom.op
      (pure _ _ U (pure _ _ U a b) c)) d) =
    g.app V.left (pure _ _ V.left
      ((tensor (tensor A B) C).presheaf.map V.hom.op
        (pure _ _ U (pure _ _ U a b) c)) d)
  simp only [pure_restrict]
  exact h _ _ _ _ _

/-- Successive degree transports compose. -/
@[simp]
lemma cast_cast {a b c : ℕ} (h : a = b) (h' : b = c) (U : X.Opens)
    (s : Piece L U a) : cast L h' U (cast L h U s) = cast L (h.trans h') U s := by
  subst b c
  rfl

/-- Transport in the left input transports the product's degree. -/
lemma mul_cast_left {a b : ℕ} (h : a = b) (n : ℕ) (U : X.Opens)
    (s : Piece L U a) (t : Piece L U n) :
    mul L U b n (cast L h U s) t =
      cast L (congrArg (· + n) h) U (mul L U a n s t) := by
  subst b
  rfl

/-- Prepend a section to a tensor-power section. -/
def cons (n : ℕ) (U : X.Opens) (s : Γ(L, U)) (t : Piece L U n) :
    Piece L U (n + 1) := pure L (tensorPower L n) U s t

/-- Transport in a tensor tail transports its successor degree. -/
lemma cons_cast {a b : ℕ} (h : a = b) (U : X.Opens)
    (s : Γ(L, U)) (t : Piece L U a) :
    cons L b U s (cast L h U t) =
      cast L (congrArg (· + 1) h) U (cons L a U s t) := by
  subst b
  rfl

/-- The recursive addition isomorphism on a pure first tensor factor. -/
lemma succ_mul_pure (m n : ℕ) (U : X.Opens)
    (s : Γ(L, U)) (t : Piece L U m) (v : Piece L U n) :
    mul L U (m + 1) n (cons L m U s t) v =
      cast L (by omega : m + n + 1 = m + 1 + n) U
        (cons L (m + n) U s (mul L U m n t v)) := by
  change (eqToIso (congrArg (tensorPower L) (show m + n + 1 = m + 1 + n by omega))).hom.app U
    ((ModuleSheafTensor.map (𝟙 L) (tensorPowerAddIso L m n).hom).app U
      ((ModuleSheafTensorAssociator.associator _ _ _).hom.app U
        (pure _ _ U (pure _ _ U s t) v))) = _
  rw [associator_hom_pure, ModuleSheafTensor.map_pure]
  rfl

/-- Tensor-power addition is associative as a morphism of sheaves. -/
lemma addIso_assoc (m n k : ℕ) :
    ModuleSheafTensor.map (tensorPowerAddIso L m n).hom (𝟙 (tensorPower L k)) ≫
      (tensorPowerAddIso L (m + n) k).hom =
    (ModuleSheafTensorAssociator.associator _ _ _).hom ≫
      ModuleSheafTensor.map (𝟙 (tensorPower L m)) (tensorPowerAddIso L n k).hom ≫
      (tensorPowerAddIso L m (n + k)).hom ≫
      (eqToIso (congrArg (tensorPower L) (Nat.add_assoc m n k).symm)).hom := by
  induction m with
  | zero =>
    apply left_hom_ext
    intro U r s t
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      ModuleSheafTensor.map_pure, associator_hom_pure, Scheme.Modules.Hom.id_app,
      ConcreteCategory.id_apply]
    change mul L U (0 + n) k (mul L U 0 n r s) t =
      cast L (Nat.add_assoc 0 n k).symm U (mul L U 0 (n + k) r (mul L U n k s t))
    rw [zero_mul, mul_cast_left, zero_mul, cast_cast, LinearMap.map_smul₂]
  | succ m ih =>
    apply four_hom_ext
    intro U a b c d
    dsimp only [tensorPower]
    have hi := congrArg (fun f ↦ f.app U (pure _ _ U (pure _ _ U b c) d)) ih
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      ModuleSheafTensor.map_pure, associator_hom_pure, Scheme.Modules.Hom.id_app,
      ConcreteCategory.id_apply] at hi
    change mul L U (m + n) k (mul L U m n b c) d =
      cast L (Nat.add_assoc m n k).symm U (mul L U m (n + k) b (mul L U n k c d)) at hi
    simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
      ModuleSheafTensor.map_pure, associator_hom_pure, Scheme.Modules.Hom.id_app,
      ConcreteCategory.id_apply]
    change mul L U (m + 1 + n) k (mul L U (m + 1) n (cons L m U a b) c) d =
      cast L (Nat.add_assoc (m + 1) n k).symm U
        (mul L U (m + 1) (n + k) (cons L m U a b) (mul L U n k c d))
    rw [succ_mul_pure, mul_cast_left, succ_mul_pure, succ_mul_pure, hi]
    rw [cons_cast]
    simp only [cast_cast]

/-- Associativity for arbitrary sections on any open. -/
lemma mul_assoc (m n k : ℕ) (U : X.Opens)
    (s : Piece L U m) (t : Piece L U n) (v : Piece L U k) :
    mul L U (m + n) k (mul L U m n s t) v =
      cast L (Nat.add_assoc m n k).symm U (mul L U m (n + k) s (mul L U n k t v)) := by
  have h := congrArg (fun f ↦ f.app U (pure _ _ U (pure _ _ U s t) v))
    (addIso_assoc L m n k)
  simp only [Scheme.Modules.Hom.comp_app, ConcreteCategory.comp_apply,
    ModuleSheafTensor.map_pure, associator_hom_pure, Scheme.Modules.Hom.id_app,
    ConcreteCategory.id_apply] at h
  exact h

end FLT.Mazur.SectionGradedMultiplication
