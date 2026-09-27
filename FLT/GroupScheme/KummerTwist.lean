/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerHopf
public import FLT.GroupScheme.QuadraticTwistComultiplication

/-!
# The quadratic twist of the Kummer model

Kummer comultiplication is cocommutative, so inversion defines the descent
action used by the quadratic twist construction.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace KummerAlgebra

variable (R : Type*) [CommRing R] (n : ℕ) (u : Rˣ) (hn : 0 < n)

/-- Evaluating the tensor components is the lift of the two component projections. -/
theorem tensorComponentsEquiv_eq_lift (i j : Fin n)
    (z : Coordinate R n u ⊗[R] Coordinate R n u) :
    tensorComponentsEquiv R n u z i j =
      Algebra.TensorProduct.lift
        (Algebra.TensorProduct.includeLeft.comp (Pi.evalAlgHom R (Component R n u) i))
        (Algebra.TensorProduct.includeRight.comp (Pi.evalAlgHom R (Component R n u) j))
        (fun _ _ ↦ .all _ _) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul a b => simp

/-- Flipping a tensor swaps the two component projection maps. -/
theorem tensorComponentsEquiv_comm_eq_lift (i j : Fin n)
    (z : Coordinate R n u ⊗[R] Coordinate R n u) :
    tensorComponentsEquiv R n u (Algebra.TensorProduct.comm R _ _ z) i j =
      Algebra.TensorProduct.lift
        (Algebra.TensorProduct.includeRight.comp (Pi.evalAlgHom R (Component R n u) j))
        (Algebra.TensorProduct.includeLeft.comp (Pi.evalAlgHom R (Component R n u) i))
        (fun _ _ ↦ .all _ _) z := by
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  | tmul a b => simp [mul_comm]

/-- The Kummer comultiplication is invariant under exchange of its tensor factors. -/
theorem comm_comul (a : Coordinate R n u) :
    Algebra.TensorProduct.comm R _ _ (comul R n u hn a) = comul R n u hn a := by
  apply (tensorComponentsEquiv R n u).injective
  funext i j
  rw [tensorComponentsEquiv_comm_eq_lift R n u i j,
    tensorComponentsEquiv_eq_lift R n u i j]
  let T := Component R n u i ⊗[R] Component R n u j
  let l : Component R n u i →ₐ[R] T := Algebra.TensorProduct.includeLeft
  let q : Component R n u j →ₐ[R] T := Algebra.TensorProduct.includeRight
  have hf := comp_rootPoint R n u l i
    (AdjoinRoot.root (equation R n u i)) (root_pow R n u i)
  have hg := comp_rootPoint R n u q j
    (AdjoinRoot.root (equation R n u j)) (root_pow R n u j)
  rw [rootPoint_root] at hf hg
  have hc : convolution R n u hn (q.comp (Pi.evalAlgHom R (Component R n u) j))
      (l.comp (Pi.evalAlgHom R (Component R n u) i)) =
    convolution R n u hn (l.comp (Pi.evalAlgHom R (Component R n u) i))
      (q.comp (Pi.evalAlgHom R (Component R n u) j)) := by
    rw [hf, hg]
    exact convolution_rootPoint_comm R n u hn _ _ _ _ _ _
  exact AlgHom.congr_fun hc a

/-- Positive-order Kummer Hopf algebras are cocommutative. -/
instance [NeZero n] : Coalgebra.IsCocomm R (Coordinate R n u) where
  comm_comp_comul := by
    apply LinearMap.ext
    intro a
    exact comm_comul R n u (Nat.pos_of_ne_zero (NeZero.ne n)) a

/-- The integral coordinate algebra proposed for an unramified quadratic twist
of Kummer torsion. -/
noncomputable def twistModel [NeZero n] (d : Rˣ) :
    Subalgebra R (QuadraticAlgebra R (d : R) 0 ⊗[R] Coordinate R n u) :=
  QuadraticTwist.model (d : R) (HopfAlgebra.antipodeAlgEquiv R (Coordinate R n u))

/-- The underlying algebra of the quadratic Kummer twist is finite flat over a Dedekind domain. -/
theorem twistModel_isFiniteFlat [IsDedekindDomain R] [NeZero n] (d : Rˣ) :
    HopfAlgebra.IsFiniteFlat R (twistModel R n u d) := by
  let _ := coordinate_finite R n u (Nat.pos_of_ne_zero (NeZero.ne n))
  let _ := coordinate_free R n u (Nat.pos_of_ne_zero (NeZero.ne n))
  exact QuadraticTwist.model_isFiniteFlat (d : R) _

/-- The quadratic Kummer twist has a comultiplication into its own tensor square. -/
noncomputable def twistComul [NeZero n] (d : Rˣ) (r : R) (hr : 2 * r = 1) :
    twistModel R n u d →ₐ[R] twistModel R n u d ⊗[R] twistModel R n u d :=
  QuadraticTwist.comul d r hr

end KummerAlgebra
