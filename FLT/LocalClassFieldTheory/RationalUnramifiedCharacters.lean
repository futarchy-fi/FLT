/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.LocalClassFieldTheory.UnramifiedCharacters
public import FLT.AbsoluteGaloisGroup.InertiaDescentHenselian

/-!
# Unramified characters at rational p-adic places

The existing completeness transport from the p-adic integers discharges the
complete-DVR hypothesis at every rational finite place. The resulting inertia
kernel comparison and normalized characters need only primality of p.
-/

@[expose] public noncomputable section

namespace LocalClassFieldTheory

open IsLocalRing NumberField

variable (p : ℕ) [Fact p.Prime]

local notation "v" => LocalCyclotomic.rationalPlace p
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
local notation "R" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ (LocalCyclotomic.rationalPlace p)
local notation "C" => AlgebraicClosure K

local instance rationalBaseComplete : IsAdicComplete (maximalIdeal R) R :=
  rationalCompletionIntegers_adicComplete p

/-- The actual rational local inertia is the kernel of the constructed unramified restriction. -/
theorem rationalUnramifiedRestriction_ker :
    (unramifiedRestriction R K C).ker = localInertiaGroup v :=
  unramifiedRestriction_ker_eq_localInertia v

/-- A continuous unramified character of any positive degree at the rational p-adic place. -/
def rationalUnramifiedCharacter (n : UnramifiedIndex) :
    Gal(C/K) →ₜ* Multiplicative (ZMod n.degree) :=
  localUnramifiedCharacter v n

/-- The rational local character is trivial on the existing valuation inertia. -/
theorem rationalUnramifiedCharacter_inertia (n : UnramifiedIndex) :
    localInertiaGroup v ≤ (rationalUnramifiedCharacter p n).toMonoidHom.ker :=
  localUnramifiedCharacter_inertia v n

/-- There is an absolute Frobenius lift on which every degree character takes the value one. -/
theorem exists_rationalUnramifiedCharacter_frobenius :
    ∃ σ : Gal(C/K), ∀ n : UnramifiedIndex,
      rationalUnramifiedCharacter p n σ = Multiplicative.ofAdd 1 := by
  obtain ⟨σ, hσ⟩ := exists_local_frobenius_lift v
  exact ⟨σ, fun n => localUnramifiedCharacter_frobenius v n σ hσ⟩

/-- Continuous inertia-trivial homomorphisms at rational places descend uniquely. -/
theorem existsUnique_rational_unramified_descent {A : Type*} [Group A] [TopologicalSpace A]
    (χ : Gal(C/K) →ₜ* A) (hχ : localInertiaGroup v ≤ χ.toMonoidHom.ker) :
    ∃! ψ : Gal(maximalUnramified R K C/K) →ₜ* A,
      ∀ σ, ψ (unramifiedRestriction R K C σ) = χ σ :=
  existsUnique_unramified_descent v χ hχ

end LocalClassFieldTheory
