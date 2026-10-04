/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.DivisionLocalInclusionLift
public import FLT.GroupScheme.PDivisibleLocalLiftDescent
public import FLT.GroupScheme.PDivisibleColimitLifting

/-! # Square-zero formal smoothness of the original p-divisible point functor -/

@[expose] public noncomputable section
namespace ThreeAdicPlan.PDivisibleSystem
variable {R K B C : Type} [CommRing R] [IsLocalRing R] [Field K] [Algebra R K]
  [PerfectField K] [IsFractionRing R K] [CommRing B] [CommRing C]
  [Algebra R B] [Algebra R C] {p height : ℕ} [Fact p.Prime]
  (X : PDivisibleSystem R K p height)

/-- Local division, infinitesimal correction and descent lift the specified original inclusion. -/
theorem exists_squareZero_inclusion_lift [Algebra B C] [IsScalarTower R B C]
    (hq : Function.Surjective (algebraMap B C))
    (hJ : RingHom.ker (algebraMap B C) ^ 2 = ⊥) (hC : IsNilpotent (p : C)) (m n : ℕ)
    (hm : ∀ b : RingHom.ker (algebraMap B C), p ^ m • b = 0)
    (x : (X.level n).CoordinateRing →ₐ[R] C) :
    ∃ y : (X.level (m + n)).CoordinateRing →ₐ[R] B,
      (IsScalarTower.toAlgHom R B C).comp y =
        x.comp (X.inclusion (Nat.le_add_left n m)).toAlgHom := by
  obtain ⟨D, _, _, _, _, hflat, y, hy⟩ := X.exists_local_inclusion_point_lift hq hJ hC m n hm x
  let := hflat
  exact X.exists_point_lift_of_flat_cover hq hJ (m + n) _ y hy

/-- Square-zero reduction is surjective on the actual point colimit when p is nilpotent. -/
theorem pointColimitMap_surjective_squareZero (q : B →ₐ[R] C)
    (hq : Function.Surjective q) (hJ : RingHom.ker q ^ 2 = ⊥) (hB : IsNilpotent (p : B)) :
    Function.Surjective (X.pointColimitMap q) := by
  let : Algebra B C := q.toRingHom.toAlgebra
  let : IsScalarTower R B C := IsScalarTower.of_algHom q
  obtain ⟨m, hm⟩ := hB
  have hC : IsNilpotent (p : C) := ⟨m, by rw [← map_natCast q, ← map_pow, hm, map_zero]⟩
  have hM (b : RingHom.ker (algebraMap B C)) : p ^ m • b = 0 := by
    apply Subtype.ext
    change p ^ m • (b : B) = 0
    rw [nsmul_eq_mul, Nat.cast_pow, hm, zero_mul]
  apply (X.pointColimitMap_surjective_iff q).mpr
  intro n x
  obtain ⟨y, hy⟩ := X.exists_squareZero_inclusion_lift hq hJ hC m n hM x
  exact ⟨m + n, Nat.le_add_left n m, y, hy⟩

end ThreeAdicPlan.PDivisibleSystem
