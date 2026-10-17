/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AdicCompletionPositiveLimit
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Constructing an actual affine target map from compatible finite coordinates

Adjacent positive-order coordinate maps determine a ring map into the original
adic completion and hence a scheme map into the specified affine target.
Every original finite coordinate map is recovered exactly.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.AdicPositiveAffineLift
universe u
variable {A C : Type u} [CommRing A] [CommRing C] (I : Ideal A)
  (f : ∀ m : ℕ, C →+* A ⧸ I ^ (m + 1))
  (hf : ∀ (m : ℕ) (x : C),
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))) (f (m + 1) x) =
      f m x)

include hf in
/-- Adjacent finite coordinates retain every positive-order restriction. -/
theorem compatible {m n : ℕ} (hmn : m ≤ n) (x : C) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)) (f n x) =
      f m x := by
  induction n, hmn using Nat.le_induction with
  | base => simp only [Ideal.Quotient.factor_eq, RingHom.id_apply]
  | succ n hmn ih =>
    rw [← Ideal.Quotient.factor_comp_apply
      (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))
      (Ideal.pow_le_pow_right (Nat.add_le_add_right hmn 1)), hf, ih]

/-- The finite coordinate maps define an actual ring map into the compatible section ring. -/
def sectionsMap : C →+* AdicCompletionPositiveLimit.sections I where
  toFun x := ⟨fun m ↦ f m x, fun hmn ↦ compatible I f hf hmn x⟩
  map_one' := Subtype.ext (funext fun m ↦ map_one (f m))
  map_mul' x y := Subtype.ext (funext fun m ↦ map_mul (f m) x y)
  map_zero' := Subtype.ext (funext fun m ↦ map_zero (f m))
  map_add' x y := Subtype.ext (funext fun m ↦ map_add (f m) x y)

/-- Reconstruct the full completed coordinate map, retaining the original complete ring. -/
def liftHom : C →+* AdicCompletion I A :=
  (AdicCompletionPositiveLimit.fromSections I).comp (sectionsMap I f hf)

/-- Each finite evaluation is the prescribed original coordinate map. -/
@[simp] theorem eval_liftHom (m : ℕ) (x : C) :
    AdicCompletion.evalₐ I (m + 1) (liftHom I f hf x) = f m x :=
  AdicCompletionPositiveLimit.eval_fromSections I m (sectionsMap I f hf x)

/-- The actual completed coordinate map is uniquely determined by these evaluations. -/
theorem liftHom_unique (g : C →+* AdicCompletion I A)
    (hg : ∀ (m : ℕ) (x : C), AdicCompletion.evalₐ I (m + 1) (g x) = f m x) :
    g = liftHom I f hf := by
  apply RingHom.ext
  intro x
  apply (AdicCompletionPositiveLimit.equivalence I).injective
  apply Subtype.ext
  funext m
  exact (hg m x).trans (eval_liftHom I f hf m x).symm

variable (X : Scheme.{u}) [IsAffine X]
  (f : ∀ m : ℕ, Γ(X, ⊤) →+* A ⧸ I ^ (m + 1))
  (hf : ∀ (m : ℕ) (x : Γ(X, ⊤)),
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (m + 1))) (f (m + 1) x) =
      f m x)

/-- The original compatible finite coordinates construct a genuine affine target morphism. -/
def lift : Spec (.of (AdicCompletion I A)) ⟶ X :=
  Spec.map (CommRingCat.ofHom (liftHom I f hf)) ≫ X.isoSpec.inv

/-- Restricting the constructed morphism to any original positive stage recovers its map. -/
@[reassoc] theorem evaluation_lift (m : ℕ) :
    Spec.map (CommRingCat.ofHom (AdicCompletion.evalₐ I (m + 1)).toRingHom) ≫
        lift I X f hf = Spec.map (CommRingCat.ofHom (f m)) ≫ X.isoSpec.inv := by
  rw [lift, ← Category.assoc, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
  congr 2
  ext x
  exact eval_liftHom I f hf m x

end FLT.Mazur.AdicPositiveAffineLift
