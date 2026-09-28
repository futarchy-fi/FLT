/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteFlatDifferentials

/-!
# Differentials of integral point images

Differential annihilation descends along a surjective algebra map. For a map
which is not surjective, a conductor element supplies a correction factor:
if `n` kills the source differentials and `c B` lies in the image, then `n c`
kills the target differentials. This does not assert that the correction
factor is a unit or has any particular valuation.
-/

@[expose] public noncomputable section

namespace KaehlerDifferential

variable {R A B : Type*} [CommRing R] [CommRing A] [CommRing B]
  [Algebra R A] [Algebra R B] [Algebra A B] [IsScalarTower R A B]

/-- Differential annihilation passes to a surjective algebra image. -/
theorem nsmul_eq_zero_of_surjective (n : ℕ)
    (hn : ∀ ω : KaehlerDifferential R A, n • ω = 0)
    (hf : Function.Surjective (algebraMap A B)) (ω : KaehlerDifferential R B) :
    n • ω = 0 := by
  obtain ⟨η, rfl⟩ := map_surjective_of_surjective R R A B hf ω
  rw [← map_nsmul, hn, map_zero]

/-- A conductor element measures the loss when passing differential annihilation
from an algebra to a larger algebra. -/
theorem nsmul_smul_eq_zero_of_conductor (n : ℕ)
    (hn : ∀ ω : KaehlerDifferential R A, n • ω = 0) (c : B)
    (hc : ∀ b : B, ∃ a : A, algebraMap A B a = c * b)
    (ω : KaehlerDifferential R B) : n • (c • ω) = 0 := by
  have himage (a : A) : n • D R B (algebraMap A B a) = 0 := by
    rw [← map_D R R A B, ← map_nsmul, hn, map_zero]
  have hmul (b : B) : n • D R B (c * b) = 0 := by
    obtain ⟨a, ha⟩ := hc b
    rw [← ha]
    exact himage a
  have hdc : n • D R B c = 0 := by simpa using hmul 1
  have hder (b : B) : n • (c • D R B b) = 0 := by
    have h := hmul b
    simpa only [Derivation.leibniz, smul_add, smul_comm n b, hdc, smul_zero, add_zero]
      using h
  have h : (n • (c • LinearMap.id) : KaehlerDifferential R B →ₗ[B]
      KaehlerDifferential R B) = 0 := by
    apply Derivation.liftKaehlerDifferential_unique
    ext b
    exact hder b
  exact LinearMap.congr_fun h ω

end KaehlerDifferential

namespace ThreeAdicPlan

variable {R K B : Type} [CommRing R] [Field K] [PerfectField K]
  [Algebra R K] [IsFractionRing R K] [CommRing B] [Algebra R B]

/-- A surjective point of a model killed by `n` has target differentials killed by `n`. -/
theorem FF.nsmul_differential_eq_zero_of_surjective_point (M : FF R K)
    (n : ℕ) (hn : KilledBy n M) (f : M.CoordinateRing →ₐ[R] B)
    (hf : Function.Surjective f) (ω : KaehlerDifferential R B) : n • ω = 0 := by
  let := f.toAlgebra
  let : IsScalarTower R M.CoordinateRing B := IsScalarTower.of_algHom f
  exact KaehlerDifferential.nsmul_eq_zero_of_surjective n
    (M.nsmul_kaehlerDifferential_eq_zero n hn) hf ω

/-- The actual image algebra of every point has differentials killed by `n`. -/
theorem FF.nsmul_differential_point_range_eq_zero (M : FF R K)
    (n : ℕ) (hn : KilledBy n M) (f : M.CoordinateRing →ₐ[R] B)
    (ω : KaehlerDifferential R f.range) : n • ω = 0 :=
  M.nsmul_differential_eq_zero_of_surjective_point n hn
    f.rangeRestrict f.rangeRestrict_surjective ω

/-- The conductor of an integral point image supplies an annihilator of the
target differentials of a model killed by `n`. -/
theorem FF.nsmul_smul_differential_eq_zero_of_point_conductor (M : FF R K)
    (n : ℕ) (hn : KilledBy n M) (f : M.CoordinateRing →ₐ[R] B) (c : B)
    (hc : ∀ b : B, ∃ a : M.CoordinateRing, f a = c * b)
    (ω : KaehlerDifferential R B) : n • (c • ω) = 0 := by
  let := f.toAlgebra
  let : IsScalarTower R M.CoordinateRing B := IsScalarTower.of_algHom f
  exact KaehlerDifferential.nsmul_smul_eq_zero_of_conductor n
    (M.nsmul_kaehlerDifferential_eq_zero n hn) c hc ω

end ThreeAdicPlan
