/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.RingTheory.Coalgebra.Convolution
public import Mathlib.RingTheory.Coalgebra.GroupLike
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.LinearAlgebra.FreeModule.Finite.Matrix
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Integral group-like elements

A generic group-like element of a finite free coalgebra over an
integrally closed domain is integral. Evaluation on that element is a character
of the finite convolution algebra of integral linear functionals; its values
are therefore integral, so every coefficient in an integral basis lies in the base.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open WithConv

namespace Coalgebra

variable {R K C : Type*} [CommRing R] [CommRing K] [Algebra R K]
  [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- Extend an integral linear functional to the scalar extension of its coalgebra. -/
def extendFunctional (f : C →ₗ[R] R) : K ⊗[R] C →ₗ[K] K :=
  (TensorProduct.AlgebraTensorModule.rid R K K).toLinearMap.comp (f.baseChange K)

omit [Coalgebra R C] in
/-- The extended functional on a pure tensor. -/
@[simp] theorem extendFunctional_tmul (f : C →ₗ[R] R) (k : K) (c : C) :
    extendFunctional f (k ⊗ₜ[R] c) = algebraMap R K (f c) * k := by
  simp [extendFunctional, Algebra.smul_def]

/-- Scalar extension respects convolution of integral functionals. -/
theorem extendFunctional_convMul (f g : WithConv (C →ₗ[R] R)) :
    extendFunctional (K := K) (f * g).ofConv =
      (toConv (extendFunctional (K := K) f.ofConv) *
        toConv (extendFunctional (K := K) g.ofConv)).ofConv := by
  ext c
  change extendFunctional (K := K) (f * g).ofConv (1 ⊗ₜ[R] c) =
    (toConv (extendFunctional (K := K) f.ofConv) *
      toConv (extendFunctional (K := K) g.ofConv)) (1 ⊗ₜ[R] c)
  simp only [extendFunctional_tmul, LinearMap.convMul_apply, TensorProduct.comul_tmul,
    CommSemiring.comul_apply]
  generalize comul (R := R) c = t
  induction t using TensorProduct.inductionOn with
  | tmul a b => simp [mul_comm]
  | add a b ha hb =>
    simpa [TensorProduct.tmul_add, map_add, add_mul] using congrArg₂ (· + ·) ha hb

/-- Extending the convolution unit gives the generic counit. -/
theorem extendFunctional_one :
    extendFunctional (K := K) (1 : WithConv (C →ₗ[R] R)).ofConv =
      counit (R := K) := by
  ext c
  simp [Algebra.smul_def]

/-- A generic group-like element evaluates the integral convolution algebra in the field. -/
def groupLikeEvaluation {x : K ⊗[R] C} (hx : IsGroupLikeElem K x) :
    WithConv (C →ₗ[R] R) →ₐ[R] K where
  toFun f := extendFunctional f.ofConv x
  map_one' := by rw [extendFunctional_one, hx.counit_eq_one]
  map_mul' f g := by
    rw [extendFunctional_convMul]
    change (toConv (extendFunctional (K := K) f.ofConv) *
      toConv (extendFunctional (K := K) g.ofConv)) x = _
    simp [hx.comul_eq_tmul_self]
  map_zero' := by simp [extendFunctional]
  map_add' f g := by simp [extendFunctional, LinearMap.baseChange_add]
  commutes' r := by
    have he : extendFunctional (K := K)
        (algebraMap R (WithConv (C →ₗ[R] R)) r).ofConv =
          algebraMap R K r • counit (R := K) := by
      ext c
      simp [Algebra.smul_def, mul_comm]
    simp [he, hx.counit_eq_one, Algebra.smul_def]

/-- Integral functionals have integral values on a generic group-like element. -/
theorem isIntegral_extendFunctional [Module.Free R C] [Module.Finite R C]
    {x : K ⊗[R] C} (hx : IsGroupLikeElem K x) (f : C →ₗ[R] R) :
    IsIntegral R (extendFunctional f x) := by
  let : Module.Finite R (WithConv (C →ₗ[R] R)) :=
    Module.Finite.equiv (WithConv.linearEquiv R (C →ₗ[R] R)).symm
  exact (Algebra.IsIntegral.isIntegral (toConv f)).map (groupLikeEvaluation hx)

omit [Coalgebra R C] in
/-- Extending a coordinate functional computes the corresponding generic coordinate. -/
theorem extendFunctional_coord {ι : Type*} (b : Module.Basis ι R C) (i : ι) :
    extendFunctional (K := K) (b.coord i) = (b.baseChange K).coord i := by
  ext c
  simp [Module.Basis.coord_apply, Algebra.smul_def]

end Coalgebra

namespace IsGroupLikeElem

/-- Extension of scalars preserves group-like elements. -/
theorem baseChange {R S C : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [AddCommGroup C] [Module R C] [Coalgebra R C] {c : C}
    (hc : IsGroupLikeElem R c) : IsGroupLikeElem S ((1 : S) ⊗ₜ[R] c) where
  counit_eq_one := by simp [hc.counit_eq_one]
  comul_eq_tmul_self := by simp [hc.comul_eq_tmul_self]

variable {R K C : Type*} [CommRing R] [IsIntegrallyClosed R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup C] [Module R C] [Coalgebra R C]

/-- Every generic group-like element of a finite free coalgebra over
an integrally closed domain comes from an integral element. -/
theorem exists_tmul_eq [Module.Free R C] [Module.Finite R C]
    {x : K ⊗[R] C} (hx : IsGroupLikeElem K x) :
    ∃ c : C, (1 : K) ⊗ₜ[R] c = x := by
  classical
  let b := Module.Free.chooseBasis R C
  have hi (i : Module.Free.ChooseBasisIndex R C) :
      ∃ r : R, algebraMap R K r = (b.baseChange K).repr x i := by
    apply IsIntegrallyClosed.isIntegral_iff.mp
    simpa only [Coalgebra.extendFunctional_coord, Module.Basis.coord_apply] using
      Coalgebra.isIntegral_extendFunctional hx (b.coord i)
  choose r hr using hi
  refine ⟨∑ i, r i • b i, ?_⟩
  apply (b.baseChange K).repr.injective
  ext i
  simp [TensorProduct.tmul_sum, TensorProduct.tmul_smul, TensorProduct.smul_tmul',
    Module.Basis.baseChange_repr_tmul, hr, Algebra.smul_def, Finsupp.single_apply]

end IsGroupLikeElem
