/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.GlobalModel
public import FLT.GroupScheme.HopfDifferentials
public import FLT.GroupScheme.RaynaudExtension

/-!
# Differentials of finite flat models killed by an integer

The killed-by condition is expressed on the specified geometric points.
Flatness and the étale generic fibre identify it with the integral Hopf-algebra
identity. The square-zero-extension calculation then annihilates the entire
module of Kähler differentials, in particular for a model killed by three.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open WithConv

namespace Bialgebra

variable (R K L H : Type) [CommRing R] [Field K] [Field L] [CommRing H]
  [Algebra R K] [Algebra K L] [Algebra R L] [IsScalarTower R K L] [Bialgebra R H]

/-- Restriction of generic points preserves the convolution monoid. -/
def restrictPointsConvMonoidHom :
    (K ⊗[R] H →ₐ[K] L) →* WithConv (H →ₐ[R] L) where
  toFun f := toConv (restrictPoints R K L H f)
  map_one' := by
    apply WithConv.ext
    ext a
    change algebraMap K L (Coalgebra.counit (R := K) ((1 : K) ⊗ₜ[R] a)) =
      algebraMap R L (Coalgebra.counit a)
    simp [Algebra.smul_def, ← IsScalarTower.algebraMap_apply R K L]
  map_mul' f g := by
    apply WithConv.ext
    rw [ofConv_toConv, restrictPoints_mul]
    ext a
    exact (AlgHom.convMul_apply _ _ _).symm

end Bialgebra

namespace ThreeAdicPlan

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]

/-- The specified integer, rather than an unspecified power, kills every geometric point. -/
def KilledBy (n : ℕ) (M : FF R K) : Prop := ∀ x : M.Points, n • x = 0

/-- A model killed by `p` is in particular killed by a power of `p`. -/
theorem KilledBy.killedByPowerOf {p : ℕ} {M : FF R K} (h : KilledBy p M) :
    KilledByPowerOf p M := ⟨1, by simpa only [pow_one, KilledBy] using h⟩

variable [PerfectField K] [IsFractionRing R K]

/-- The abelian geometric point group forces the integral comultiplication to be cocommutative. -/
theorem FF.coordinateRing_cocomm (M : FF R K) : Coalgebra.IsCocomm R M.CoordinateRing :=
  cocomm_of_injective_points M.points.toAddMonoidHom M.points_bijective.1

/-- A killed-by identity on geometric points holds on the integral Hopf algebra. -/
theorem FF.id_convPow_eq_one (M : FF R K) (n : ℕ) (hn : KilledBy n M) :
    toConv (AlgHom.id R M.CoordinateRing) ^ n =
      (1 : WithConv (M.CoordinateRing →ₐ[R] M.CoordinateRing)) := by
  apply WithConv.ext
  ext a
  apply Algebra.eq_of_generic_points_eq R K (AlgebraicClosure K) M.CoordinateRing
  intro f
  have hf : toConv f ^ n = 1 := by
    obtain ⟨q, rfl⟩ :=
      (Bialgebra.restrictPoints R K (AlgebraicClosure K) M.CoordinateRing).surjective f
    have hq : q ^ n = 1 := by
      apply Additive.ofMul.injective
      apply M.points_bijective.1
      change M.points (n • Additive.ofMul q) = M.points 0
      rw [map_nsmul, map_zero]
      exact hn _
    exact (map_pow (Bialgebra.restrictPointsConvMonoidHom R K (AlgebraicClosure K)
      M.CoordinateRing) q n).symm.trans (by rw [hq, map_one])
  have hc := congrArg (fun g : M.CoordinateRing →ₐ[R] AlgebraicClosure K => g a)
    (HopfAlgebra.comp_convPow f (AlgHom.id R M.CoordinateRing) n)
  simpa only [AlgHom.comp_id, hf, AlgHom.comp_apply, AlgHom.convOne_apply, AlgHom.commutes] using hc

/-- A finite flat model killed by `n` has its entire module of differentials killed by `n`. -/
theorem FF.nsmul_kaehlerDifferential_eq_zero (M : FF R K) (n : ℕ) (hn : KilledBy n M)
    (ω : KaehlerDifferential R M.CoordinateRing) : n • ω = 0 := by
  let := M.coordinateRing_cocomm
  exact HopfAlgebra.nsmul_kaehlerDifferential_eq_zero n (M.id_convPow_eq_one n hn) ω

/-- The Hopf-algebra differential annihilation needed in the killed-by-three case of Fontaine. -/
theorem FF.three_smul_kaehlerDifferential_eq_zero (M : FF ℤ_[3] ℚ_[3]) (hM : KilledBy 3 M)
    (ω : KaehlerDifferential ℤ_[3] M.CoordinateRing) : (3 : ℤ_[3]) • ω = 0 := by
  calc
    (3 : ℤ_[3]) • ω = (3 : ℕ) • ω := Nat.cast_smul_eq_nsmul ℤ_[3] 3 ω
    _ = 0 := M.nsmul_kaehlerDifferential_eq_zero 3 hM ω

end ThreeAdicPlan
