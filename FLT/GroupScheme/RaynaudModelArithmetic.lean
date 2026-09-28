/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GlobalModel
public import FLT.GroupScheme.RaynaudRankThreeExtension

/-!
# Addition and multiplication on finite flat models

Convolution constructs addition of integral model morphisms. Restriction to the
generic fibre preserves addition, so multiplication by an integer is integral.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open WithConv

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
    [PerfectField K] [IsFractionRing R K]

/-- The abelian generic point group forces the integral model to be cocommutative. -/
instance FF.cocomm (X : FF R K) : Coalgebra.IsCocomm R X.CoordinateRing :=
  cocomm_of_injective_points X.points.toAddMonoidHom X.points_bijective.1

/-- The zero group morphism, represented by the counit followed by the unit. -/
def ModelHom.zero (X Y : FF R K) : ModelHom X Y :=
  (1 : WithConv (Y.CoordinateRing →ₐc[R] X.CoordinateRing)).ofConv

/-- Addition of model morphisms, represented by convolution of coordinate maps. -/
def ModelHom.add {X Y : FF R K} (f g : ModelHom X Y) : ModelHom X Y :=
  (toConv f * toConv g).ofConv

/-- Integral multiplication by a natural number, represented by convolution powers. -/
def FF.multiply (X : FF R K) (n : ℕ) : ModelHom X X :=
  (toConv (BialgHom.id R X.CoordinateRing) ^ n).ofConv

omit [PerfectField K] [IsFractionRing R K] in
/-- Restriction to integral coordinates commutes with precomposition by a model map. -/
theorem ModelHom.restrictPoints_baseChange {X Y : FF R K} (f : ModelHom X Y)
    (p : K ⊗[R] X.CoordinateRing →ₐ[K] AlgebraicClosure K) :
    Bialgebra.restrictPoints R K (AlgebraicClosure K) Y.CoordinateRing
      (p.comp f.baseChange.toAlgHom) =
    (Bialgebra.restrictPoints R K (AlgebraicClosure K) X.CoordinateRing p).comp
      f.toAlgHom := rfl

omit [PerfectField K] [IsFractionRing R K] in
/-- The zero integral morphism induces zero on generic points. -/
@[simp] theorem ModelHom.genericHom_zero (X Y : FF R K) (x : X.Points) :
    genericHom (ModelHom.zero X Y) x = 0 := by
  obtain ⟨p, rfl⟩ := X.points_bijective.2 x
  rw [genericHom_points, ← map_zero Y.points]
  congr 1
  apply Additive.toMul.injective
  apply AlgHom.ext
  intro a
  induction a using TensorProduct.inductionOn with
  | tmul k a =>
    change p.toMul (k ⊗ₜ[R] algebraMap R X.CoordinateRing (Coalgebra.counit a)) = _
    change p.toMul (k ⊗ₜ[R] algebraMap R X.CoordinateRing (Coalgebra.counit a)) =
      algebraMap K (AlgebraicClosure K) (Coalgebra.counit (k ⊗ₜ[R] a))
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    change p.toMul (algebraMap K _ ((Coalgebra.counit (R := R) a) • k)) = _
    rw [AlgHom.commutes, TensorProduct.counit_tmul]
    simp [Algebra.smul_def, mul_comm]
  | add a b ha hb => simpa only [map_add] using congrArg₂ (· + ·) ha hb

/-- Addition of integral morphisms induces pointwise addition on generic points. -/
@[simp] theorem ModelHom.genericHom_add {X Y : FF R K} (f g : ModelHom X Y)
    (x : X.Points) : genericHom (f.add g) x = genericHom f x + genericHom g x := by
  obtain ⟨p, rfl⟩ := X.points_bijective.2 x
  rw [genericHom_points, genericHom_points, genericHom_points, ← map_add]
  congr 1
  apply Additive.toMul.injective
  apply (Bialgebra.restrictPoints R K (AlgebraicClosure K) Y.CoordinateRing).injective
  change Bialgebra.restrictPoints R K (AlgebraicClosure K) Y.CoordinateRing
      (p.toMul.comp (f.add g).baseChange.toAlgHom) =
    Bialgebra.restrictPoints R K (AlgebraicClosure K) Y.CoordinateRing
      ((p.toMul.comp f.baseChange.toAlgHom) * (p.toMul.comp g.baseChange.toAlgHom))
  rw [Bialgebra.restrictPoints_mul]
  change (Bialgebra.restrictPoints R K (AlgebraicClosure K) X.CoordinateRing p.toMul).comp
      (f.add g).toAlgHom = _
  let q := Bialgebra.restrictPoints R K (AlgebraicClosure K) X.CoordinateRing p.toMul
  have he := AlgHom.comp_convMul_distrib q (toConv f.toAlgHom) (toConv g.toAlgHom)
  exact he.trans (by
    ext a
    exact AlgHom.convMul_apply (toConv (q.comp f.toAlgHom))
      (toConv (q.comp g.toAlgHom)) a)

/-- Multiplication by a natural number on a model induces ordinary multiplication
on its generic point group. -/
@[simp] theorem FF.genericHom_multiply (X : FF R K) (n : ℕ) (x : X.Points) :
    genericHom (X.multiply n) x = n • x := by
  induction n with
  | zero =>
    simp only [FF.multiply, pow_zero, zero_nsmul]
    exact ModelHom.genericHom_zero X X x
  | succ n hn =>
    have he : X.multiply (n + 1) = (X.multiply n).add (BialgHom.id R X.CoordinateRing) := by
      simp only [FF.multiply, ModelHom.add, pow_succ, toConv_ofConv]
    rw [he, ModelHom.genericHom_add, hn, genericHom_id, add_nsmul, one_nsmul]

/-- Integral multiplication vanishes exactly when it annihilates all generic points. -/
theorem FF.multiply_eq_zero_iff (X : FF R K) (n : ℕ) :
    X.multiply n = ModelHom.zero X X ↔ ∀ x : X.Points, n • x = 0 := by
  constructor
  · intro h x
    have he := congrArg (fun f : ModelHom X X ↦ genericHom f x) h
    simpa only [FF.genericHom_multiply, ModelHom.genericHom_zero] using he
  · intro h
    apply genericHom_injective
    ext x
    simpa only [FF.genericHom_multiply, ModelHom.genericHom_zero] using h x

/-- The pointwise prime-power annihilator is equivalent to integral annihilation. -/
theorem FF.killedByPowerOf_iff_multiply (X : FF R K) (p : ℕ) :
    KilledByPowerOf p X ↔ ∃ n : ℕ, X.multiply (p ^ n) = ModelHom.zero X X := by
  simp only [KilledByPowerOf, FF.multiply_eq_zero_iff]

end ThreeAdicPlan
