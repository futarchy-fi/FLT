/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SheafPullbackCoordinateRefinement
public import FLT.Mazur.AffineOpenCoverTestRecovery

/-!
# A sealed interface for affine-test refinement

Keep the actual pullback equation behind a small proposition while transporting
large quotient-sheaf expressions. The gluing construction consumes that equation.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.SheafPullbackRefinementLaw
open SheafPullbackPathComparison SheafPullbackCoordinateRefinement
universe u
variable {S T X : Scheme.{u}} {P Q : X.Modules}
variable (t : S ⟶ T) (z : T ⟶ X) (z' : S ⟶ X) (h : t ≫ z = z')

/-- The original geometric refinement equation, sealed for use with large sheaf expressions. -/
@[irreducible] def Refines
    (a : (pullback z).obj P ⟶ (pullback z).obj Q)
    (a' : (pullback z').obj P ⟶ (pullback z').obj Q) : Prop :=
  (pullback t).map a ≫ (comparison t z z' h).hom.app Q =
    (comparison t z z' h).hom.app P ≫ a'

/-- Equality of the two test maps preserves their refinement law. -/
theorem Refines.congr_maps
    {a b : (pullback z).obj P ⟶ (pullback z).obj Q}
    {a' b' : (pullback z').obj P ⟶ (pullback z').obj Q}
    (ha : a = b) (ha' : a' = b') (hr : Refines t z z' h b b') :
    Refines t z z' h a a' := by
  subst b b'
  exact hr

/-- Recover the exact scheme-pullback equation from the sealed law. -/
theorem Refines.equation
    {a : (pullback z).obj P ⟶ (pullback z).obj Q}
    {a' : (pullback z').obj P ⟶ (pullback z').obj Q}
    (hr : Refines t z z' h a a') :
    (pullback t).map a ≫ (comparison t z z' h).hom.app Q =
      (comparison t z z' h).hom.app P ≫ a' := by
  unfold Refines at hr
  exact hr

/-- Coherent named coordinates give coherent maps on the actual tests. -/
theorem coordinate_refines {Y Z : Scheme.{u}}
    (p : X ⟶ Y) (q : X ⟶ Z) (f : T ⟶ Y) (g : T ⟶ Z)
    (hf : z ≫ p = f) (hg : z ≫ q = g)
    (f' : S ⟶ Y) (g' : S ⟶ Z) (hf' : z' ≫ p = f') (hg' : z' ≫ q = g')
    (htf : t ≫ f = f') (htg : t ≫ g = g') {M : Y.Modules} {N : Z.Modules}
    (a : (pullback f).obj M ⟶ (pullback g).obj N)
    (a' : (pullback f').obj M ⟶ (pullback g').obj N)
    (ha : (pullback t).map a ≫ (comparison t g g' htg).hom.app N =
      (comparison t f f' htf).hom.app M ≫ a') :
    Refines t z z' h (coordinateMap z p q f g hf hg a)
      (coordinateMap z' p q f' g' hf' hg' a') := by
  unfold Refines
  exact coordinateMap_refine z p q f g hf hg t z' h f' g' hf' hg' htf htg a a' ha

variable (U : X.AffineOpenCover)
variable (a : ∀ {A : CommRingCat.{u}} (f : Spec A ⟶ X),
  (pullback f).obj P ⟶ (pullback f).obj Q)
variable (ha : ∀ {A B : CommRingCat.{u}} (f : Spec A ⟶ X)
  (g : Spec B ⟶ X) (α : A ⟶ B) (w : Spec.map α ≫ f = g),
  Refines (Spec.map α) f g w (a f) (a g))
variable (hiso : ∀ i, IsIso (a (U.f i)))

/-- The sealed refinement laws glue the actual isomorphisms on the entire scheme. -/
def glueIso : P ≅ Q :=
  AffineOpenCoverCommonRefinement.comparisonIso U a
    (fun f g α w ↦ Refines.equation _ _ _ _ (ha f g α w)) hiso

/-- The glued map retains the prescribed value on every affine test. -/
theorem glueIso_test {A : CommRingCat.{u}} (f : Spec A ⟶ X) :
    (pullback f).map (glueIso U a ha hiso).hom = a f :=
  AffineOpenCoverCommonRefinement.comparisonIso_test U a
    (fun f g α w ↦ Refines.equation _ _ _ _ (ha f g α w)) hiso f

end FLT.Mazur.SheafPullbackRefinementLaw
