/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Descent

/-!
# Tensor overlap cocycles and scalar-extension coalgebras

The two affine overlap modules are written as `N ⊗[R] S` and `S ⊗[R] N`.
The cocycle equation is imposed on all three tensor factors. Evaluating it
at the two unit factors gives the comultiplication law.
-/

@[expose] public noncomputable section

open CategoryTheory TensorProduct

universe u

namespace FLT.Mazur.AffineTensorCocycle

variable {R S N : Type u} [CommRing R] [CommRing S] [Algebra R S]
  [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N]

/-- Insert an element in the middle of a threefold tensor product. -/
def insertMiddle (s : S) : S ⊗[R] N →ₗ[R] S ⊗[R] (S ⊗[R] N) :=
  (TensorProduct.mk R S N s).lTensor S

/-- The first two overlap transports, composed over the triple overlap. -/
def transportTwice (e : N ⊗[R] S ≃ₗ[S] S ⊗[R] N) :
    (N ⊗[R] S) ⊗[R] S →ₗ[R] S ⊗[R] (S ⊗[R] N) :=
  (e.toLinearMap.restrictScalars R).lTensor S ∘ₗ
    (TensorProduct.assoc R S N S).toLinearMap ∘ₗ
      (e.toLinearMap.restrictScalars R).rTensor S

/-- An overlap isomorphism with both scalar actions, diagonal, and triple cocycle.
These are equations on the given isomorphism, without a descended-module witness. -/
structure Datum (R S N : Type u) [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup N] [Module R N] [Module S N] [IsScalarTower R S N] where
  /-- The overlap transport; the first scalar action is preserved by linearity. -/
  overlap : N ⊗[R] S ≃ₗ[S] S ⊗[R] N
  /-- Compatibility with the other scalar action of the double overlap. -/
  other_smul (n : N) (s t : S) :
    overlap (n ⊗ₜ[R] (s * t)) =
      (Algebra.lsmul R R N s).lTensor S (overlap (n ⊗ₜ[R] t))
  /-- Restriction to the diagonal is the identity. -/
  diagonal (n : N) :
    TensorProduct.lift (Algebra.lsmul R R N (A := S)).toLinearMap (overlap (n ⊗ₜ[R] (1 : S))) = n
  /-- The two consecutive transports equal the direct transport over the triple overlap. -/
  cocycle (n : N) (s t : S) :
    transportTwice overlap ((n ⊗ₜ[R] s) ⊗ₜ[R] t) =
      insertMiddle s (overlap (n ⊗ₜ[R] t))

namespace Datum

variable (D : Datum R S N)

/-- The coaction is overlap transport evaluated at the unit of the second factor. -/
def coaction : N →ₗ[S] S ⊗[R] N where
  toFun n := D.overlap (n ⊗ₜ[R] (1 : S))
  map_add' n m := by rw [add_tmul, map_add]
  map_smul' s n := by rw [← smul_tmul', map_smul]; rfl

@[simp]
theorem coaction_apply (n : N) : D.coaction n = D.overlap (n ⊗ₜ[R] (1 : S)) := rfl

/-- The diagonal identity gives the counit equation. -/
theorem coaction_counit (n : N) :
    TensorProduct.lift (Algebra.lsmul R R N (A := S)).toLinearMap (D.coaction n) = n :=
  D.diagonal n

/-- The triple-overlap equation gives the coassociativity equation. -/
theorem coaction_coassoc (n : N) :
    (D.coaction.restrictScalars R).lTensor S (D.coaction n) =
      insertMiddle (1 : S) (D.coaction n) := by
  have h := D.cocycle n 1 1
  change _ = insertMiddle (1 : S) (D.coaction n) at h
  rw [← h]
  change _ = ((D.overlap.toLinearMap.restrictScalars R).lTensor S)
    ((TensorProduct.assoc R S N S) ((D.coaction n) ⊗ₜ[R] (1 : S)))
  generalize D.coaction n = x
  induction x using TensorProduct.inductionOn with
  | tmul s n => rfl
  | add x y hx hy => simp only [map_add, add_tmul, hx, hy]

/-- The second scalar action recovers the full overlap map from its coaction. -/
theorem overlap_tmul (n : N) (s : S) :
    D.overlap (n ⊗ₜ[R] s) =
      (Algebra.lsmul R R N s).lTensor S (D.coaction n) := by
  simpa only [mul_one, coaction_apply] using D.other_smul n s 1

/-- The coaction retains the specified overlap isomorphism, not only its class. -/
theorem overlap_eq_of_coaction_eq {E : Datum R S N} (h : D.coaction = E.coaction) :
    D.overlap = E.overlap := by
  apply LinearEquiv.toLinearMap_injective
  apply AlgebraTensorModule.ext
  intro n s
  simp only [LinearEquiv.coe_coe, D.overlap_tmul, E.overlap_tmul, h]

end Datum

section Coalgebra

variable {A B : CommRingCat.{u}} (φ : A ⟶ B) (M : ModuleCat.{u} B)


set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-- A tensor-overlap cocycle defines an actual scalar-extension coalgebra. -/
def toCoalgebra :
    letI := φ.hom.toAlgebra
    letI := Module.compHom M φ.hom
    letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
    Datum A B M → (ModuleCat.extendRestrictScalarsAdj φ.hom).toComonad.Coalgebra := by
  letI := φ.hom.toAlgebra
  letI := Module.compHom M φ.hom
  letI : IsScalarTower A B M := IsScalarTower.of_algebraMap_smul (fun _ _ ↦ rfl)
  intro D
  exact {
    A := M
    a := ModuleCat.ofHom D.coaction
    counit := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro n
      exact D.coaction_counit n
    coassoc := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro n
      exact (D.coaction_coassoc n).symm }

end Coalgebra

end FLT.Mazur.AffineTensorCocycle
