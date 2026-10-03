/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ContinuousKummerClass
public import FLT.GaloisRepresentation.Extensions.CharacterBasis

/-!
# Unit classes under cyclic coefficient changes

Raising roots to a natural power corresponds to multiplying additive root
coefficients by that integer. Powers invertible modulo n preserve and
reflect the independent valuation-unit subgroup. This is a cyclic
coefficient result, not an arbitrary finite-field scalar-extension theorem.
-/

@[expose] public section

namespace KummerTheory

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {n : ℕ}

/-- Integer scaling of additive root coefficients is powering of units. -/
@[simp] theorem rootUnit_nsmul (m : ℕ) (x : RootModule L n) :
    rootUnit (m • x) = rootUnit x ^ m := rfl

/-- Powers of a root give the correspondingly scaled cocycle. -/
theorem rootCocycle_pow (q : Kˣ) (b : Lˣ)
    (hb : b ^ n = Units.map (algebraMap K L) q) (m : ℕ)
    (hm : (b ^ m) ^ n = Units.map (algebraMap K L) (q ^ m)) (g : Gal(L/K)) :
    rootCocycle (q ^ m) (b ^ m) hm g = m • rootCocycle q b hb g := by
  apply rootUnit_injective
  simp only [rootUnit_nsmul, rootUnit_rootCocycle, unitRatio, smul_pow', div_pow]

/-- The power class group is killed by n. -/
theorem powerClass_pow_n (x : PowerClass K n) : x ^ n = 1 := by
  induction x using Quotient.inductionOn with | h q =>
    change (powerClassMap n q) ^ n = 1
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr ⟨q, rfl⟩

/-- Invertible powers preserve and reflect valuation-unit classes. -/
theorem isUnitClass_pow_iff (A : ValuationSubring K) (x : PowerClass K n)
    (m t k : ℕ) (hmt : m * t = 1 + n * k) :
    IsUnitClass A n (x ^ m) ↔ IsUnitClass A n x := by
  constructor
  · intro hx
    have hxt := (unitClasses A n).pow_mem hx t
    rw [← pow_mul, hmt, pow_add, pow_one, pow_mul, powerClass_pow_n, one_pow, mul_one] at hxt
    exact hxt
  · intro hx
    exact (unitClasses A n).pow_mem hx m

/-- The same criterion on representatives is invariant under a cyclic basis change. -/
theorem isUnitClass_parameter_pow_iff (A : ValuationSubring K) (q : Kˣ)
    (m t k : ℕ) (hmt : m * t = 1 + n * k) :
    IsUnitClass A n (powerClassMap n (q ^ m)) ↔ IsUnitClass A n (powerClassMap n q) := by
  rw [map_pow]
  exact isUnitClass_pow_iff A _ m t k hmt

open GaloisRepresentation.Extensions

/-- The inverse exponent acts as an inverse on root coefficients. -/
theorem rootScale_inverse (m t k : ℕ) (hmt : m * t = 1 + n * k)
    (x : RootModule L n) : t • (m • x) = x := by
  apply rootUnit_injective
  rw [rootUnit_nsmul, rootUnit_nsmul, ← pow_mul, hmt, pow_add, pow_one,
    pow_mul, rootUnit_pow, one_pow, mul_one]

/-- An exponent invertible modulo n gives an additive coefficient equivalence. -/
def rootScaleEquiv (m t k : ℕ) (hmt : m * t = 1 + n * k) :
    RootModule L n ≃+ RootModule L n where
  toFun x := m • x
  invFun x := t • x
  left_inv := rootScale_inverse m t k hmt
  right_inv := rootScale_inverse t m k (by simpa only [Nat.mul_comm] using hmt)
  map_add' x y := nsmul_add x y m

/-- Cyclic coefficient changes commute with the Galois action. -/
theorem rootScaleEquiv_equivariant (m t k : ℕ) (hmt : m * t = 1 + n * k)
    (g : Gal(L/K)) (x : RootModule L n) :
    rootScaleEquiv (L := L) m t k hmt (g • x) = g • rootScaleEquiv m t k hmt x := by
  apply rootUnit_injective
  change rootUnit (m • (g • x)) = rootUnit (g • (m • x))
  simp only [rootUnit_nsmul, rootUnit_smul, smul_pow']

variable [IsGalois K L]

/-- The class transport under a cyclic basis change agrees with powering the parameter. -/
theorem rootScale_class (q : Kˣ) (b : Lˣ)
    (hb : b ^ n = Units.map (algebraMap K L) q)
    (m t k : ℕ) (hmt : m * t = 1 + n * k)
    (hp : (b ^ m) ^ n = Units.map (algebraMap K L) (q ^ m)) :
    mapCoefficientClass (rootScaleEquiv m t k hmt)
      (rootScaleEquiv_equivariant (K := K) m t k hmt)
      (continuousClassMk (continuousRootCocycle q b hb)) =
        continuousClassMk (continuousRootCocycle (q ^ m) (b ^ m) hp) := by
  apply congrArg continuousClassMk
  apply Subtype.ext
  apply ContinuousMap.ext
  intro g
  exact (rootCocycle_pow q b hb m hp g).symm

/-- Kummer's quotient map intertwines cyclic coefficient transport with powering. -/
theorem kummerClassMap_rootScale
    (roots : ∀ q : Kˣ, ∃ b : Lˣ, b ^ n = Units.map (algebraMap K L) q)
    (m t k : ℕ) (hmt : m * t = 1 + n * k) (x : PowerClass K n) :
    mapCoefficientClass (rootScaleEquiv m t k hmt)
      (rootScaleEquiv_equivariant (K := K) m t k hmt) (kummerClassMap roots x) =
        kummerClassMap roots (x ^ m) := by
  induction x using Quotient.inductionOn with | h q =>
    let b := (roots q).choose
    have hb := (roots q).choose_spec
    have hp : (b ^ m) ^ n = Units.map (algebraMap K L) (q ^ m) := by
      rw [pow_right_comm, hb, map_pow]
    change _ = kummerClassMap roots ((powerClassMap n q) ^ m)
    rw [← map_pow, kummerClassMap_mk]
    change mapCoefficientClass _ _ (continuousClassMk (continuousRootCocycle q b hb)) = _
    rw [rootScale_class q b hb m t k hmt hp]
    exact continuousRootCocycle_independent (q ^ m) (b ^ m) _ hp (roots (q ^ m)).choose_spec

variable [NeZero n]
    (roots : ∀ q : Kˣ, ∃ b : Lˣ, b ^ n = Units.map (algebraMap K L) q)

/-- Unit membership of a continuous root class, through the proved Kummer equivalence. -/
def IsUnitContinuousClass (A : ValuationSubring K)
    (z : ContinuousClass Gal(L/K) (RootModule L n)) : Prop :=
  IsUnitClass A n ((continuousKummerEquiv roots).symm z)

/-- Cyclic basis changes preserve and reflect unit membership of continuous classes. -/
theorem isUnitContinuousClass_rootScale_iff (A : ValuationSubring K)
    (m t k : ℕ) (hmt : m * t = 1 + n * k)
    (z : ContinuousClass Gal(L/K) (RootModule L n)) :
    IsUnitContinuousClass roots A (mapCoefficientClass (rootScaleEquiv m t k hmt)
      (rootScaleEquiv_equivariant (K := K) m t k hmt) z) ↔ IsUnitContinuousClass roots A z := by
  obtain ⟨x, rfl⟩ := kummerClassMap_surjective roots z
  rw [kummerClassMap_rootScale]
  change IsUnitClass A n
    ((continuousKummerEquiv roots).symm (continuousKummerEquiv roots (x ^ m))) ↔
    IsUnitClass A n ((continuousKummerEquiv roots).symm (continuousKummerEquiv roots x))
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]
  exact isUnitClass_pow_iff A x m t k hmt

end KummerTheory
