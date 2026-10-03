/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedCharacterDescent
public import FLT.LocalClassFieldTheory.UnramifiedCyclicStages

/-!
# Normalized continuous unramified characters

At a number-field completion with adically complete integers, the constructed
positive-degree characters are continuous and trivial on valuation inertia.
They take every lift of arithmetic Frobenius to one. The target is written
multiplicatively so that a character on a Galois group is a monoid homomorphism;
its underlying value is the usual additive Z/n-valued character.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing NumberField

variable {F : Type} [Field F] [NumberField F]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F))

local notation "K" => v.adicCompletion F
local notation "R" => v.adicCompletionIntegers F
local notation "C" => AlgebraicClosure K

variable [IsAdicComplete (maximalIdeal (v.adicCompletionIntegers F))
  (v.adicCompletionIntegers F)]

/-- The continuous character of degree n on the local absolute Galois group. -/
def localUnramifiedCharacter (n : UnramifiedIndex) :
    Gal(C/K) →ₜ* Multiplicative (ZMod n.degree) :=
  (unramifiedDegreeCharacter R K C n).comp
    ⟨unramifiedRestriction R K C, unramifiedRestriction_continuous R K C⟩

/-- Valuation inertia acts trivially under every constructed degree character. -/
theorem localUnramifiedCharacter_inertia (n : UnramifiedIndex) :
    localInertiaGroup v ≤ (localUnramifiedCharacter v n).toMonoidHom.ker := by
  intro σ hσ
  have h : unramifiedRestriction R K C σ = 1 := by
    change σ ∈ (unramifiedRestriction R K C).ker
    rwa [unramifiedRestriction_ker_eq_localInertia v]
  change unramifiedDegreeCharacter R K C n (unramifiedRestriction R K C σ) = 1
  rw [h, map_one]

/-- The normalization holds for every absolute automorphism lifting arithmetic Frobenius. -/
theorem localUnramifiedCharacter_frobenius (n : UnramifiedIndex) (σ : Gal(C/K))
    (hσ : unramifiedRestriction R K C σ = unramifiedFrobenius R K C) :
    localUnramifiedCharacter v n σ = Multiplicative.ofAdd 1 := by
  change unramifiedDegreeCharacter R K C n (unramifiedRestriction R K C σ) = _
  rw [hσ, unramifiedDegreeCharacter_frobenius]

/-- Arithmetic Frobenius has an absolute lift, so the normalization condition is realized. -/
theorem exists_local_frobenius_lift :
    ∃ σ : Gal(C/K), unramifiedRestriction R K C σ = unramifiedFrobenius R K C :=
  unramifiedRestriction_surjective R K C (unramifiedFrobenius R K C)

/-- In additive notation the character law is addition in Z/n. -/
theorem localUnramifiedCharacter_mul (n : UnramifiedIndex) (σ τ : Gal(C/K)) :
    (localUnramifiedCharacter v n (σ * τ)).toAdd =
      (localUnramifiedCharacter v n σ).toAdd + (localUnramifiedCharacter v n τ).toAdd :=
  congrArg Multiplicative.toAdd (map_mul (localUnramifiedCharacter v n) σ τ)

end LocalClassFieldTheory
