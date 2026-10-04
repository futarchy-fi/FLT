/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedScalarDescent
public import FLT.LocalClassFieldTheory.UnramifiedUnitAnnihilator

/-!
# The prime-root peu-ramification predicate and independent units

The original continuous cup-annihilator predicate, for the actual unramified
restriction kernel, is equivalent to being the Kummer class of an integral
unit. The two definitions are kept independent throughout the proof.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

namespace LocalClassFieldTheory

open IsLocalRing KummerTheory GaloisRepresentation.Extensions

attribute [local instance] relativeBaseTower unramifiedUnionGalois fieldUnitAction
  unramifiedFieldUnitTopology unramifiedFieldUnitDiscrete
  separableClosureGalois separableClosureUnitTopology separableClosureUnitDiscrete

variable (R K C : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  [Field C] [IsAlgClosed C] [Algebra K C] [Algebra R C] [IsScalarTower R K C]
  [Algebra.IsSeparable K C] [Finite (ResidueField R)] [CharZero C]
  [IsAdicComplete (maximalIdeal R) R]
  (q : ℕ) [Fact q.Prime]

local notation "U" => maximalUnramified R K C
local notation "I" => MonoidHom.ker (unramifiedRestriction R K C)
local notation "κ" => kummerClassMap (exists_unit_root (K := K) (L := C) (n := q))

omit [CharZero C] in
/-- Descent identifies the independent inertia-trivial character test with the quotient test. -/
theorem isPeuRamifiedCocycle_unramified_iff (c : ContinuousCocycle Gal(C/K) (RootModule C q)) :
    IsPeuRamifiedCocycle (k := ZMod q) I c ↔
      ∀ χ : ContinuousScalarCharacter Gal(U/K) (ZMod q),
        ContinuousIsCoboundaryTwo
          (continuousCup c (inflatedUnramifiedScalarCharacter R K C χ)) := by
  constructor
  · intro h χ
    exact h _ (inflatedUnramifiedScalarCharacter_unramified R K C χ)
  · intro h χ hχ
    obtain ⟨ψ, rfl⟩ := exists_unramifiedScalar_descent R K C χ hχ
    exact h ψ

variable (p : ℕ) [Fact p.Prime] [CharP (ResidueField R) p]

include p in
/-- The actual Kummer parameter class is peu-ramified exactly when it has a unit representative. -/
theorem isPeuRamified_parameter_iff_unit_power (a : Kˣ) :
    IsPeuRamifiedClass (k := ZMod q) I (κ (powerClassMap q a)) ↔
      ∃ (b : Kˣ) (u : Rˣ), a = b ^ q * Units.map (algebraMap R K) u := by
  change IsPeuRamifiedCocycle (k := ZMod q) I
    (continuousRootCocycle a (kummerCarryRoot K C q a) (kummerCarryRoot_pow K C q a)) ↔ _
  rw [isPeuRamifiedCocycle_unramified_iff]
  exact unramifiedKummer_annihilator_iff_unit R K C q p a

include p in
/-- The independent prime-root predicate holds exactly on the integral-unit image. -/
theorem isPeuRamifiedClass_iff_unit_image
    (x : ContinuousClass Gal(C/K) (RootModule C q)) :
    IsPeuRamifiedClass (k := ZMod q) I x ↔
      ∃ u : Rˣ, x = κ (powerClassMap q (Units.map (algebraMap R K) u)) := by
  obtain ⟨y, rfl⟩ := kummerClassMap_surjective
    (exists_unit_root (K := K) (L := C) (n := q)) x
  induction y using Quotient.inductionOn with | h a =>
    change IsPeuRamifiedClass (k := ZMod q) I (κ (powerClassMap q a)) ↔ _
    rw [isPeuRamified_parameter_iff_unit_power R K C q p]
    constructor
    · rintro ⟨b, u, rfl⟩
      exact ⟨u, congrArg κ (powerClassMap_pow_mul q b _)⟩
    · rintro ⟨u, hu⟩
      have he := kummerClassMap_injective (exists_unit_root (K := K) (L := C) (n := q)) hu
      obtain ⟨b, hb⟩ := QuotientGroup.eq_iff_div_mem.mp he
      refine ⟨b, u, ?_⟩
      change b ^ q = a / Units.map (algebraMap R K) u at hb
      rw [hb, div_mul_cancel]

end LocalClassFieldTheory
