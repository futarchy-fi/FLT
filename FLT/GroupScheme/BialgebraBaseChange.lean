/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat
/-!
# Successive scalar extensions of bialgebras

The usual cancellation and congruence maps for scalar extension preserve counit
and comultiplication, so arithmetic models can use them as bialgebra comparisons.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
open scoped TensorProduct
namespace ThreeAdicPlan
variable (R S T A : Type) [CommRing R] [CommRing S] [CommRing T] [CommRing A]
    [Algebra R S] [Algebra R T] [Algebra S T] [IsScalarTower R S T]
    [Bialgebra R A]
/-- Successive scalar extensions cancel as bialgebras. -/
def bialgebraCancelBaseChange : T ⊗[S] (S ⊗[R] A) ≃ₐc[T] T ⊗[R] A := by
  let E := Algebra.TensorProduct.cancelBaseChange R S T T A
  refine BialgEquiv.ofAlgEquiv E ?_ ?_
  · apply Algebra.TensorProduct.ext_ring
    apply Algebra.TensorProduct.ext_ring
    ext a
    simp [E, TensorProduct.counit_tmul, Algebra.smul_def,
      IsScalarTower.algebraMap_apply R S T]
  · apply Algebra.TensorProduct.ext_ring
    apply Algebra.TensorProduct.ext_ring
    ext a
    change Algebra.TensorProduct.map E.toAlgHom E.toAlgHom
      (Coalgebra.comul (R := T) (1 ⊗ₜ[S] (1 ⊗ₜ[R] a))) =
        Coalgebra.comul (R := T) (E (1 ⊗ₜ[S] (1 ⊗ₜ[R] a)))
    dsimp only [E]
    rw [Algebra.TensorProduct.cancelBaseChange_tmul, one_smul]
    simp only [TensorProduct.comul_tmul, CommSemiring.comul_apply]
    generalize Coalgebra.comul (R := R) a = z
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp
    | add x y hx hy => simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy

/-- A bialgebra equivalence remains an equivalence after scalar extension. -/
def bialgebraBaseChangeEquiv (B : Type) [CommRing B] [Bialgebra R B]
    (e : A ≃ₐc[R] B) : S ⊗[R] A ≃ₐc[S] S ⊗[R] B :=
  BialgEquiv.ofBijective
    (Bialgebra.TensorProduct.map (BialgHom.id S S) e.toBialgHom)
    (Algebra.TensorProduct.congr (AlgEquiv.refl : S ≃ₐ[S] S) e.toAlgEquiv).bijective

variable (R S H A : Type) [CommRing R] [CommRing S] [CommRing H] [CommRing A]
    [Algebra R S] [Bialgebra R H] [Bialgebra S A] [Algebra R A]
    [IsScalarTower R S A]

/-- The tensor-square map induced by a homomorphism with different coefficient rings. -/
def bialgebraScalarTensorMap (f : H →ₐ[R] A) : H ⊗[R] H →ₐ[R] A ⊗[S] A :=
  Algebra.TensorProduct.lift
    (((Algebra.TensorProduct.includeLeft : A →ₐ[S] A ⊗[S] A).restrictScalars R).comp f)
    (((Algebra.TensorProduct.includeRight : A →ₐ[S] A ⊗[S] A).restrictScalars R).comp f)
    (fun _ _ ↦ Commute.all _ _)

/-- A scalar-extension algebra comparison respecting the restricted Hopf operations
is a bialgebra comparison. -/
def bialgebraScalarExtensionEquiv (f : H →ₐ[R] A) (E : S ⊗[R] H ≃ₐ[S] A)
    (hE : ∀ a, E (1 ⊗ₜ[R] a) = f a)
    (hε : ∀ a, algebraMap R S (Coalgebra.counit (R := R) a) =
      Coalgebra.counit (R := S) (f a))
    (hΔ : ∀ a, bialgebraScalarTensorMap R S H A f (Coalgebra.comul (R := R) a) =
      Coalgebra.comul (R := S) (f a)) : S ⊗[R] H ≃ₐc[S] A := by
  refine BialgEquiv.ofAlgEquiv E ?_ ?_
  · apply Algebra.TensorProduct.ext_ring
    ext a
    change Coalgebra.counit (R := S) (E (1 ⊗ₜ[R] a)) =
      Coalgebra.counit (R := S) (1 ⊗ₜ[R] a : S ⊗[R] H)
    rw [hE, TensorProduct.counit_tmul, CommSemiring.counit_apply]
    simpa [Algebra.smul_def] using (hε a).symm
  · apply Algebra.TensorProduct.ext_ring
    ext a
    change Algebra.TensorProduct.map E.toAlgHom E.toAlgHom
      (Coalgebra.comul (R := S) (1 ⊗ₜ[R] a : S ⊗[R] H)) =
      Coalgebra.comul (R := S) (E (1 ⊗ₜ[R] a))
    rw [hE, ← hΔ]
    simp only [TensorProduct.comul_tmul, CommSemiring.comul_apply]
    generalize Coalgebra.comul (R := R) a = z
    induction z using TensorProduct.inductionOn with
    | tmul x y => simp [bialgebraScalarTensorMap, hE]
    | add x y hx hy => simpa [TensorProduct.tmul_add] using congrArg₂ (· + ·) hx hy

end ThreeAdicPlan
