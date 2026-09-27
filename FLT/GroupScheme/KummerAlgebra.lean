/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlat
public import Mathlib.RingTheory.AdjoinRoot
public import Mathlib.RingTheory.Etale.StandardEtale
public import Mathlib.RingTheory.TensorProduct.Pi

/-!
# Coordinate algebra of a Kummer extension

For a unit `u` and a positive integer `n`, the components of the Kummer
extension of `ℤ/nℤ` by `μₙ` have equations `X ^ n = u ^ i`.
This file constructs their coordinate algebra and proves it is finite free.
The module-theoretic finite-flat property does not supply a Hopf structure.
-/

@[expose] public section

set_option backward.isDefEq.respectTransparency false

open Polynomial

namespace KummerAlgebra

variable (R : Type*) [CommRing R] (n : ℕ) (u : Rˣ)

/-- The equation of component `i` of the Kummer extension. -/
noncomputable def equation (i : Fin n) : R[X] := X ^ n - C ((u : R) ^ i.val)

/-- The coordinate ring of one Kummer component. -/
abbrev Component (i : Fin n) := AdjoinRoot (equation R n u i)

/-- The coordinate ring of the disjoint union of the Kummer components. -/
abbrev Coordinate := (i : Fin n) → Component R n u i

/-- Every component equation is monic when the torsion order is positive. -/
theorem equation_monic (hn : 0 < n) (i : Fin n) : (equation R n u i).Monic :=
  monic_X_pow_sub_C _ (ne_of_gt hn)

/-- A Kummer component is a free module over the coefficient ring. -/
theorem component_free (hn : 0 < n) (i : Fin n) : Module.Free R (Component R n u i) :=
  (equation_monic R n u hn i).free_adjoinRoot

/-- A Kummer component is a finite module over the coefficient ring. -/
theorem component_finite (hn : 0 < n) (i : Fin n) :
    Module.Finite R (Component R n u i) :=
  (equation_monic R n u hn i).finite_adjoinRoot

/-- The complete Kummer coordinate ring is free over the coefficient ring. -/
theorem coordinate_free (hn : 0 < n) : Module.Free R (Coordinate R n u) := by
  let _ (i : Fin n) := component_free R n u hn i
  infer_instance

/-- The complete Kummer coordinate ring is finite over the coefficient ring. -/
theorem coordinate_finite (hn : 0 < n) : Module.Finite R (Coordinate R n u) := by
  let _ (i : Fin n) := component_finite R n u hn i
  infer_instance

/-- The Kummer coordinate ring satisfies the module-theoretic finite-flat condition,
including when `n` is not invertible in the coefficient ring. -/
theorem coordinate_isFiniteFlat (hn : 0 < n) :
    HopfAlgebra.IsFiniteFlat R (Coordinate R n u) := by
  let _ := coordinate_free R n u hn
  let _ := coordinate_finite R n u hn
  exact ⟨⟩

/-- The distinguished coordinate on a Kummer component satisfies its equation. -/
theorem root_pow (i : Fin n) :
    AdjoinRoot.root (equation R n u i) ^ n =
      algebraMap R (Component R n u i) ((u : R) ^ i.val) := by
  have h := AdjoinRoot.eval₂_root (equation R n u i)
  change eval₂ _ _ (X ^ n - C ((u : R) ^ i.val)) = 0 at h
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  exact sub_eq_zero.mp h

/-- The distinguished coordinate is a unit, also in residue characteristic dividing `n`. -/
theorem root_isUnit (hn : 0 < n) (i : Fin n) :
    IsUnit (AdjoinRoot.root (equation R n u i)) := by
  apply (isUnit_pow_iff hn.ne').mp
  rw [root_pow]
  exact (u.isUnit.pow i.val).map (algebraMap R (Component R n u i))

variable {S : Type*} [CommRing S] [Algebra R S]

/-- A solution of the component equation defines an algebra map from its coordinate ring. -/
noncomputable def componentPoint (i : Fin n) (x : S)
    (hx : x ^ n = algebraMap R S ((u : R) ^ i.val)) : Component R n u i →ₐ[R] S :=
  AdjoinRoot.liftAlgHom _ (Algebra.ofId R S) x (by simpa [equation] using sub_eq_zero.mpr hx)

/-- The component algebra map sends the distinguished coordinate to the specified root. -/
@[simp] theorem componentPoint_root (i : Fin n) (x : S)
    (hx : x ^ n = algebraMap R S ((u : R) ^ i.val)) :
    componentPoint R n u i x hx (AdjoinRoot.root (equation R n u i)) = x :=
  AdjoinRoot.liftAlgHom_root _ _ _ _

/-- Algebra maps from one component are exactly the solutions of its defining equation. -/
noncomputable def componentPointsEquiv (i : Fin n) :
    (Component R n u i →ₐ[R] S) ≃
      {x : S // x ^ n = algebraMap R S ((u : R) ^ i.val)} where
  toFun f := ⟨f (AdjoinRoot.root (equation R n u i)), by
    rw [← map_pow, root_pow, f.commutes]⟩
  invFun x := componentPoint R n u i x.val x.property
  left_inv f := by ext; simp
  right_inv x := by ext; simp

/-- The component algebra is étale whenever the torsion order is invertible. -/
theorem component_etale (hn : 0 < n) (hunit : IsUnit (n : R)) (i : Fin n) :
    Algebra.Etale R (Component R n u i) := by
  let f := equation R n u i
  let P : StandardEtalePair R :=
    ⟨f, equation_monic R n u hn i, f.derivative, 1, 0, 1, by simp⟩
  have hd : IsUnit (AdjoinRoot.mk f f.derivative) := by
    rw [← AdjoinRoot.aeval_eq]
    change IsUnit (aeval (AdjoinRoot.root f) ((X ^ n - C ((u : R) ^ i.val)).derivative))
    rw [derivative_sub, derivative_X_pow, derivative_C, sub_zero,
      map_mul, map_pow, aeval_C, aeval_X]
    exact (hunit.map (algebraMap R (Component R n u i))).mul
      ((root_isUnit R n u hn i).pow (n - 1))
  let e : P.Ring ≃ₐ[R] Component R n u i :=
    P.equivAwayAdjoinRoot.trans
      ((IsLocalization.atUnit (AdjoinRoot f) _ _ hd).symm.restrictScalars R)
  exact Algebra.Etale.of_equiv e

/-- The Kummer algebra is étale when the torsion order is invertible. -/
theorem coordinate_etale (hn : 0 < n) (hunit : IsUnit (n : R)) :
    Algebra.Etale R (Coordinate R n u) := by
  let _ (i : Fin n) := component_etale R n u hn hunit i
  infer_instance

open scoped TensorProduct in
/-- Base change of a Kummer component is the component with the mapped parameter. -/
noncomputable def componentBaseChange :
    ∀ i : Fin n, S ⊗[R] Component R n u i ≃ₐ[S]
      Component S n (Units.map (algebraMap R S) u) i := by
  intro i
  let v := Units.map (algebraMap R S).toMonoidHom u
  let A := Component S n v i
  let x := AdjoinRoot.root (equation S n v i)
  have hx : x ^ n = algebraMap R A ((u : R) ^ i.val) := by
    rw [root_pow]
    change algebraMap S A ((algebraMap R S (u : R)) ^ i.val) = _
    rw [← map_pow, ← IsScalarTower.algebraMap_apply]
  let f : S ⊗[R] Component R n u i →ₐ[S] A :=
    Algebra.TensorProduct.lift (Algebra.ofId S A)
      (componentPoint R n u i x hx) (fun _ _ ↦ .all _ _)
  let g : A →ₐ[S] S ⊗[R] Component R n u i :=
    componentPoint S n v i (1 ⊗ₜ[R] AdjoinRoot.root (equation R n u i)) (by
      rw [Algebra.TensorProduct.tmul_pow, one_pow, root_pow]
      change 1 ⊗ₜ[R] algebraMap R (Component R n u i) ((u : R) ^ i.val) =
        ((algebraMap R S (u : R)) ^ i.val) ⊗ₜ[R] (1 : Component R n u i)
      rw [← map_pow]
      simp only [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul,
        TensorProduct.smul_tmul])
  have hgx : g x = 1 ⊗ₜ[R] AdjoinRoot.root (equation R n u i) :=
    componentPoint_root S n v i _ _
  have hfx : f (1 ⊗ₜ[R] AdjoinRoot.root (equation R n u i)) = x := by
    dsimp only [f]
    rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul, componentPoint_root]
  exact AlgEquiv.ofAlgHom f g
    (by
      ext
      change f (g x) = x
      rw [hgx, hfx])
    (by
      ext
      change g (f (1 ⊗ₜ[R] AdjoinRoot.root (equation R n u i))) = _
      rw [hfx, hgx]
      rfl)

open scoped TensorProduct in
/-- Base change commutes with the complete Kummer coordinate algebra. -/
noncomputable def coordinateBaseChange :
    S ⊗[R] Coordinate R n u ≃ₐ[S] Coordinate S n (Units.map (algebraMap R S) u) :=
  (Algebra.TensorProduct.piRight R S S (Component R n u)).trans
    (AlgEquiv.piCongrRight (componentBaseChange R n u))

open scoped TensorProduct in
/-- The generic fibre is étale as soon as the torsion order is invertible there,
even when it is not invertible over the original coefficient ring. -/
theorem generic_etale (hn : 0 < n) (hunit : IsUnit (n : S)) :
    Algebra.Etale S (S ⊗[R] Coordinate R n u) := by
  let _ := coordinate_etale S n (Units.map (algebraMap R S) u) hn hunit
  exact Algebra.Etale.of_equiv (coordinateBaseChange R n u).symm

end KummerAlgebra
