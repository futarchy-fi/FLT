/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.NumberTheory.NumberField.Ideal.Basic
public import Mathlib.NumberTheory.RamificationInertia.Galois
public import Mathlib.NumberTheory.RamificationInertia.Unramified
public import Mathlib.RingTheory.Frobenius
import Mathlib.RingTheory.Flat.TorsionFree

/-!
# Frobenius order and residue degree

This proves leaf B1 of `docs/CHEBOTAREV_PLAN.md`. At an unramified prime, the
inertia group is trivial, so the decomposition group's action on the residue
field is faithful. The order of a Frobenius element is therefore the order of
the finite-field Frobenius, which is the residue degree.

`frob K L v` chooses a prime above `v` and uses Mathlib's arithmetic Frobenius.
`orderOf_frob_eq_inertiaDeg` applies to every prime above `v`, since residue
degrees are constant in a Galois extension. The auxiliary
`orderOf_eq_inertiaDeg_of_isArithFrobAt` also applies to other Frobenius choices.
-/

@[expose] public section

open NumberField
open scoped Pointwise

namespace GaloisRepresentation.Chebotarev

/-- A nonzero prime ideal of the ring of integers of a number field. -/
@[nolint unusedArguments]
abbrev Prime (K : Type*) [Field K] [NumberField K] :=
  IsDedekindDomain.HeightOneSpectrum (𝓞 K)

variable (K L : Type*) [Field K] [NumberField K] [Field L] [NumberField L]
  [Algebra K L]

/-- A prime of `K` is unramified in `L` if all primes above it are unramified. -/
def Unram (v : Prime K) : Prop := Algebra.IsUnramifiedIn (𝓞 L) v.asIdeal

/-- Every nonzero prime of `K` has a nonzero prime above it in `L`. -/
theorem exists_primeAbove (v : Prime K) :
    ∃ w : Prime L, w.asIdeal.under (𝓞 K) = v.asIdeal := by
  obtain ⟨Q, hQ, hQv⟩ :=
    Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 L) v.asIdeal
  exact ⟨⟨Q, hQ.isPrime, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q⟩, hQv.over.symm⟩

/-- A chosen nonzero prime of `L` above `v`. -/
noncomputable def primeAbove (v : Prime K) : Prime L :=
  (exists_primeAbove K L v).choose

/-- The chosen prime contracts to `v`. -/
@[simp]
theorem primeAbove_under (v : Prime K) :
    (primeAbove K L v).asIdeal.under (𝓞 K) = v.asIdeal :=
  (exists_primeAbove K L v).choose_spec

variable [IsGalois K L]

/-- Arithmetic Frobenius at the chosen prime of `L` above `v`. -/
noncomputable def frob (v : Prime K) : Gal(L/K) :=
  arithFrobAt (𝓞 K) Gal(L/K) (primeAbove K L v).asIdeal

/-- The chosen Frobenius satisfies the residue congruence at the chosen prime. -/
theorem isArithFrobAt_frob (v : Prime K) :
    IsArithFrobAt (𝓞 K) (frob K L v) (primeAbove K L v).asIdeal :=
  IsArithFrobAt.arithFrobAt _ _ _

/-- The inertia group at an unramified prime of a Galois extension is trivial. -/
theorem inertia_eq_bot_of_isUnramifiedAt (w : Prime L)
    [Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal] :
    w.asIdeal.inertia Gal(L/K) = ⊥ := by
  apply Subgroup.eq_bot_of_card_eq
  rw [Ideal.card_inertia_eq_ramificationIdxIn (w.asIdeal.under (𝓞 K)) w.asIdeal,
    Ideal.ramificationIdxIn_eq_ramificationIdx _ w.asIdeal Gal(L/K)]
  exact Ideal.ramificationIdx_eq_one_of_isUnramifiedAt

attribute [local instance] Ideal.Quotient.field in
/-- Every arithmetic Frobenius at an unramified prime has order equal to its
residue degree. -/
theorem orderOf_eq_inertiaDeg_of_isArithFrobAt (w : Prime L) (σ : Gal(L/K))
    (hσ : IsArithFrobAt (𝓞 K) σ w.asIdeal)
    [Algebra.IsUnramifiedAt (𝓞 K) w.asIdeal] :
    orderOf σ = w.asIdeal.inertiaDeg (𝓞 K) := by
  have hi := inertia_eq_bot_of_isUnramifiedAt K L w
  let P := w.asIdeal.under (𝓞 K)
  let f := Ideal.Quotient.stabilizerHom w.asIdeal P Gal(L/K)
  let σ' : MulAction.stabilizer Gal(L/K) w.asIdeal := ⟨σ, hσ.mem_stabilizer⟩
  have hf : Function.Injective f := by
    apply (MonoidHom.ker_eq_bot_iff f).mp
    apply le_antisymm _ bot_le
    intro g hg
    apply Subtype.ext
    have hg' : g.val ∈ w.asIdeal.inertia Gal(L/K) := by
      rw [← Ideal.Quotient.map_ker_stabilizer_subtype w.asIdeal P Gal(L/K)]
      exact ⟨g, hg, rfl⟩
    simpa [hi] using hg'
  let : Fintype ((𝓞 K) ⧸ P) := Fintype.ofFinite _
  have he : f σ' = FiniteField.frobeniusAlgEquivOfAlgebraic ((𝓞 K) ⧸ P)
      ((𝓞 L) ⧸ w.asIdeal) := by
    ext x
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    simpa [f, σ', Nat.card_eq_fintype_card] using hσ.mk_apply x
  calc
    orderOf σ = orderOf σ' :=
      orderOf_injective (MulAction.stabilizer Gal(L/K) w.asIdeal).subtype
        Subtype.val_injective σ'
    _ = orderOf (f σ') := (orderOf_injective f hf σ').symm
    _ = Module.finrank ((𝓞 K) ⧸ P) ((𝓞 L) ⧸ w.asIdeal) := by
      rw [he, FiniteField.orderOf_frobeniusAlgEquivOfAlgebraic]
    _ = w.asIdeal.inertiaDeg (𝓞 K) :=
      (Ideal.inertiaDeg_eq_of_isMaximal P w.asIdeal).symm

/-- At an unramified prime, the chosen Frobenius has order equal to the residue
degree of any prime above it. -/
theorem orderOf_frob_eq_inertiaDeg (v : Prime K) (w : Prime L)
    (hw : w.asIdeal.under (𝓞 K) = v.asIdeal) (hu : Unram K L v) :
    orderOf (frob K L v) = w.asIdeal.inertiaDeg (𝓞 K) := by
  let : w.asIdeal.LiesOver v.asIdeal := ⟨hw.symm⟩
  let : (primeAbove K L v).asIdeal.LiesOver v.asIdeal := ⟨(primeAbove_under K L v).symm⟩
  let : Algebra.IsUnramifiedAt (𝓞 K) (primeAbove K L v).asIdeal := hu _ inferInstance inferInstance
  exact (orderOf_eq_inertiaDeg_of_isArithFrobAt K L _ _ (isArithFrobAt_frob K L v)).trans
    (Ideal.inertiaDeg_eq_of_isGaloisGroup v.asIdeal _ w.asIdeal Gal(L/K))

/-- Frobenius is trivial exactly when every prime above the unramified prime
has residue degree one. -/
theorem frob_eq_one_iff (v : Prime K) (hu : Unram K L v) :
    frob K L v = 1 ↔ ∀ w : Prime L, w.asIdeal.under (𝓞 K) = v.asIdeal →
      w.asIdeal.inertiaDeg (𝓞 K) = 1 := by
  constructor
  · intro h w hw
    rw [← orderOf_frob_eq_inertiaDeg K L v w hw hu, h, orderOf_one]
  · intro h
    apply orderOf_eq_one_iff.mp
    rw [orderOf_frob_eq_inertiaDeg K L v (primeAbove K L v) (primeAbove_under K L v) hu]
    exact h _ (primeAbove_under K L v)

end GaloisRepresentation.Chebotarev
