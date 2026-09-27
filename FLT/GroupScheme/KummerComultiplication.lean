/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.KummerAlgebra

/-!
# Multiplication maps for the Kummer model

Multiplication of Kummer points carries the component indices modulo `n` and
divides the product of the root coordinates by `u` for each carry. These maps
are defined over the coefficient ring without inverting `n`.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open scoped TensorProduct

namespace KummerAlgebra

variable (R : Type*) [CommRing R] (n : ℕ) (u : Rˣ)

/-- The component reached by adding two component indices. -/
def sumComponent (hn : 0 < n) (i j : Fin n) : Fin n :=
  ⟨(i.val + j.val) % n, Nat.mod_lt _ hn⟩

/-- The Kummer multiplication formula preserves the component equation. -/
theorem mul_carry_pow {S : Type*} [CommRing S] [Algebra R S]
    {x y : S} {i j k c : ℕ}
    (hx : x ^ n = algebraMap R S ((u : R) ^ i))
    (hy : y ^ n = algebraMap R S ((u : R) ^ j))
    (hi : i + j = k + n * c) :
    (x * y * algebraMap R S ((↑u⁻¹ : R) ^ c)) ^ n =
      algebraMap R S ((u : R) ^ k) := by
  have hu : u ^ (i + j) * (u⁻¹) ^ (c * n) = u ^ k := by
    rw [hi, Nat.mul_comm c n]
    simp [pow_add, mul_assoc]
  have hv := congrArg (fun z : Rˣ ↦ algebraMap R S (z : R)) hu
  simpa only [mul_pow, hx, hy, ← map_pow, ← map_mul, ← pow_add,
    ← pow_mul, Units.val_mul, Units.val_pow_eq_pow_val] using hv

/-- The root coordinate in the tensor product corresponding to Kummer multiplication. -/
noncomputable def multiplicationRoot (i j : Fin n) :
    Component R n u i ⊗[R] Component R n u j :=
  ((Algebra.TensorProduct.includeLeft : Component R n u i →ₐ[R]
      Component R n u i ⊗[R] Component R n u j) (AdjoinRoot.root (equation R n u i))) *
    ((Algebra.TensorProduct.includeRight : Component R n u j →ₐ[R]
      Component R n u i ⊗[R] Component R n u j) (AdjoinRoot.root (equation R n u j))) *
      algebraMap R _ ((↑u⁻¹ : R) ^ ((i.val + j.val) / n))

/-- The proposed multiplication coordinate is a root of the target component equation. -/
theorem multiplicationRoot_pow (hn : 0 < n) (i j : Fin n) :
    multiplicationRoot R n u i j ^ n =
      algebraMap R _ ((u : R) ^ (sumComponent n hn i j).val) := by
  unfold multiplicationRoot
  apply mul_carry_pow R n u
  · rw [← map_pow, root_pow, AlgHom.commutes]
  · rw [← map_pow, root_pow, AlgHom.commutes]
  · exact (Nat.mod_add_div (i.val + j.val) n).symm

/-- Pullback of Kummer multiplication on a pair of components. -/
noncomputable def componentComul (hn : 0 < n) (i j : Fin n) :
    Component R n u (sumComponent n hn i j) →ₐ[R]
      Component R n u i ⊗[R] Component R n u j :=
  componentPoint R n u _ (multiplicationRoot R n u i j)
    (multiplicationRoot_pow R n u hn i j)

/-- The component multiplication map has the prescribed value on the root coordinate. -/
@[simp] theorem componentComul_root (hn : 0 < n) (i j : Fin n) :
    componentComul R n u hn i j
      (AdjoinRoot.root (equation R n u (sumComponent n hn i j))) =
      multiplicationRoot R n u i j :=
  componentPoint_root R n u _ _ _

/-- Tensor products distribute over the components of the Kummer algebra. -/
noncomputable def tensorComponentsEquiv :
    Coordinate R n u ⊗[R] Coordinate R n u ≃ₐ[R]
      ((i j : Fin n) → Component R n u i ⊗[R] Component R n u j) :=
  (Algebra.TensorProduct.comm R (Coordinate R n u) (Coordinate R n u)).trans <|
    (Algebra.TensorProduct.piRight R R (Coordinate R n u) (Component R n u)).trans <|
      AlgEquiv.piCongrRight fun i ↦
        (Algebra.TensorProduct.comm R (Coordinate R n u) (Component R n u i)).trans
          (Algebra.TensorProduct.piRight R R (Component R n u i) (Component R n u))

/-- Comultiplication on the Kummer coordinate algebra, assembled from the carry formula. -/
noncomputable def comul (hn : 0 < n) :
    Coordinate R n u →ₐ[R] Coordinate R n u ⊗[R] Coordinate R n u :=
  (tensorComponentsEquiv R n u).symm.toAlgHom.comp <|
    AlgHom.pi fun i ↦ AlgHom.pi fun j ↦
      (componentComul R n u hn i j).comp
        (Pi.evalAlgHom R (Component R n u) (sumComponent n hn i j))

/-- In component coordinates, comultiplication is the prescribed Kummer multiplication map. -/
@[simp] theorem comul_component (hn : 0 < n) (f : Coordinate R n u) (i j : Fin n) :
    tensorComponentsEquiv R n u (comul R n u hn f) i j =
      componentComul R n u hn i j (f (sumComponent n hn i j)) := by
  simp [comul]

/-- The counit evaluates component zero at the root `1`. -/
noncomputable def counit (hn : 0 < n) : Coordinate R n u →ₐ[R] R :=
  (componentPoint R n u ⟨0, hn⟩ 1 (by simp)).comp
    (Pi.evalAlgHom R (Component R n u) ⟨0, hn⟩)

end KummerAlgebra
