/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.ContinuousKummerParameter
public import FLT.GroupScheme.KummerRootClass

/-!
# Continuous Kummer comparison

Continuous root classes identify with power classes when the Galois
extension contains nth roots of all base-field units. Root existence is an
explicit arithmetic hypothesis, not a consequence of being Galois.
-/

@[expose] public section

namespace KummerTheory

open GaloisRepresentation.Extensions

variable {K L : Type*} [Field K] [Field L] [Algebra K L] [IsGalois K L]
    {n : ℕ}

/-- Two root cocycles differ by a splitting precisely when their parameters have the same class. -/
theorem rootCocycle_equivalent_iff (q r : Kˣ) (b d : Lˣ)
    (hb : b ^ n = Units.map (algebraMap K L) q)
    (hd : d ^ n = Units.map (algebraMap K L) r) :
    SplittingEquivalent (rootCocycle q b hb) (rootCocycle r d hd) ↔
      powerClassMap n q = powerClassMap n r := by
  let i : Kˣ →* Lˣ := Units.map (algebraMap K L).toMonoidHom
  have hi : Function.Injective i := fun x y h ↦ Units.ext
    ((algebraMap K L).injective (congrArg (fun u : Lˣ ↦ (u : L)) h))
  constructor
  · rintro ⟨x, hx⟩
    have he : unitRatio (K := K) (b * rootUnit x) = unitRatio d := by
      funext g
      rw [unitRatio_mul]
      have h := congrArg rootUnit (congrFun hx g)
      simpa only [changeSplitting, rootUnit_add, rootUnit_sub, rootUnit_smul,
        rootUnit_rootCocycle, unitRatio] using h.symm
    obtain ⟨t, ht⟩ := (unitRatio_eq_iff (b * rootUnit x) d).mp he
    have hb' : b ^ n = i q := hb
    have hd' : d ^ n = i r := hd
    have ht' : d = b * rootUnit x * i t := ht
    have hr : r = q * t ^ n := hi (by
      rw [← hd', ht', mul_pow, mul_pow, rootUnit_pow, mul_one, hb', map_mul, map_pow])
    rw [hr, mul_comm q, powerClassMap_pow_mul]
  · intro h
    obtain ⟨t, ht⟩ := QuotientGroup.eq_iff_div_mem.mp h.symm
    change t ^ n = r / q at ht
    have hp : (d / (b * i t)) ^ n = 1 := by
      rw [div_pow, mul_pow, hd, hb, ← map_pow, ht, map_div]
      change i r / (i q * (i r / i q)) = 1
      simp
    let x := rootOfUnit (d / (b * i t)) hp
    refine ⟨x, funext fun g ↦ ?_⟩
    apply rootUnit_injective
    change unitRatio d g = unitRatio b g * (g • (d / (b * i t)) / (d / (b * i t)))
    have htfix : g • i t = i t := by
      apply Units.ext
      exact g.commutes (t : K)
    simp only [unitRatio, smul_div', smul_mul', htfix]
    simp [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

variable (roots : ∀ q : Kˣ, ∃ b : Lˣ, b ^ n = Units.map (algebraMap K L) q)

/-- The continuous class of a parameter, independent of the root selected here. -/
noncomputable def parameterClass (q : Kˣ) : ContinuousClass Gal(L/K) (RootModule L n) :=
  continuousClassMk (continuousRootCocycle q (roots q).choose (roots q).choose_spec)

/-- Parameter-class equality detects exactly equality modulo nth powers. -/
theorem parameterClass_eq_iff (q r : Kˣ) :
    parameterClass roots q = parameterClass roots r ↔ powerClassMap n q = powerClassMap n r := by
  rw [parameterClass, parameterClass, continuousClassMk_eq_iff]
  exact rootCocycle_equivalent_iff q r _ _ (roots q).choose_spec (roots r).choose_spec

/-- Kummer's map on power classes, formed from the explicit continuous cocycle quotient. -/
noncomputable def kummerClassMap : PowerClass K n → ContinuousClass Gal(L/K) (RootModule L n) :=
  Quotient.lift (parameterClass roots) (fun q r h ↦
    (parameterClass_eq_iff roots q r).mpr (Quotient.sound h))

/-- The map sends a unit class to the class of its root ratio. -/
@[simp] theorem kummerClassMap_mk (q : Kˣ) :
    kummerClassMap roots (powerClassMap n q) = parameterClass roots q := rfl

/-- The Kummer comparison is injective. -/
theorem kummerClassMap_injective : Function.Injective (kummerClassMap roots) := by
  intro x y
  induction x using Quotient.inductionOn with | h q =>
    induction y using Quotient.inductionOn with | h r =>
      intro h
      exact (parameterClass_eq_iff roots q r).mp h

variable [NeZero n]

/-- Finite Hilbert 90 proves surjectivity of the continuous comparison. -/
theorem kummerClassMap_surjective : Function.Surjective (kummerClassMap roots) := by
  intro z
  induction z using Quotient.inductionOn with | h c =>
    obtain ⟨q, b, hb, heq⟩ := exists_continuous_unit_parameter
      (fun g ↦ c.1 g) c.2 c.1.continuous
    refine ⟨powerClassMap n q, ?_⟩
    rw [kummerClassMap_mk]
    have hc : continuousRootCocycle q b hb = c := by
      apply Subtype.ext
      apply ContinuousMap.ext
      intro g
      exact rootUnit_injective (heq g)
    change continuousClassMk _ = _
    rw [continuousRootCocycle_independent q (roots q).choose b (roots q).choose_spec hb, hc]
    rfl

/-- Power classes and continuous root cocycle classes are equivalent. -/
noncomputable def continuousKummerEquiv :
    PowerClass K n ≃ ContinuousClass Gal(L/K) (RootModule L n) :=
  Equiv.ofBijective (kummerClassMap roots)
    ⟨kummerClassMap_injective roots, kummerClassMap_surjective roots⟩

end KummerTheory
