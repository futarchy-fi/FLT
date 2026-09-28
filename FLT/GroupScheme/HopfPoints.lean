/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat
public import Mathlib.RingTheory.HopfAlgebra.Convolution

/-!
# The group structure on geometric Hopf-algebra points

The raw algebra-homomorphism type already has convolution multiplication.
For a cocommutative Hopf algebra, its antipode supplies inverses and
cocommutativity makes convolution commutative.
-/

@[expose] public noncomputable section

open scoped TensorProduct

namespace HopfAlgebra

variable (K L A : Type) [Field K] [Field L] [Algebra K L]
  [CommRing A] [HopfAlgebra K A] [Coalgebra.IsCocomm K A]

/-- The existing convolution monoid of points is a commutative group. -/
@[instance_reducible]
def pointsCommGroup : CommGroup (A →ₐ[K] L) where
  toMonoid := inferInstance
  inv f := f.comp (antipodeAlgHom K A)
  inv_mul_cancel f := by
    change (Algebra.TensorProduct.lift (f.comp (antipodeAlgHom K A)) f
      (fun _ _ ↦ Commute.all _ _)).comp (Bialgebra.comulAlgHom K A) =
      (Algebra.ofId K L).comp (Bialgebra.counitAlgHom K A)
    have h : Algebra.TensorProduct.lift (f.comp (antipodeAlgHom K A)) f
        (fun _ _ ↦ Commute.all _ _) = f.comp
        ((Algebra.TensorProduct.lmul' K).comp
          (Algebra.TensorProduct.map (antipodeAlgHom K A) (AlgHom.id K A))) := by
      ext <;> simp
    rw [h, AlgHom.comp_assoc, AlgHom.comp_assoc]
    have hc := congrArg WithConv.ofConv (AlgHom.antipode_id_cancel (R := K) (A := A))
    change (Algebra.TensorProduct.lmul' K).comp
      ((Algebra.TensorProduct.map (antipodeAlgHom K A) (AlgHom.id K A)).comp
        (Bialgebra.comulAlgHom K A)) =
      (Algebra.ofId K A).comp (Bialgebra.counitAlgHom K A) at hc
    rw [hc]
    ext
    simp
  mul_comm f g := by
    apply AlgHom.ext
    intro a
    have h := congrArg (Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _))
      (Coalgebra.comm_comul (R := K) a)
    change Algebra.TensorProduct.lift f g (fun _ _ ↦ Commute.all _ _)
        (Coalgebra.comul a) =
      Algebra.TensorProduct.lift g f (fun _ _ ↦ Commute.all _ _) (Coalgebra.comul a)
    rw [← h]
    induction Coalgebra.comul (R := K) a using TensorProduct.inductionOn with
    | tmul x y => simp [mul_comm]
    | add x y hx hy => simp only [map_add, hx, hy]

end HopfAlgebra
