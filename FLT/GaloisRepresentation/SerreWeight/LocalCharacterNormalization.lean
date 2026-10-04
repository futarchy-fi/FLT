/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.LocalCyclotomicSurjectivity
public import FLT.GaloisRepresentation.SerreWeight.CoefficientCharacterExponent
public import FLT.GaloisRepresentation.Extensions.CharacterLines

/-!
# Local character normalization and its unramified factor

The actual cyclotomic character is surjective on rational p-adic inertia.
Kernel containment therefore extracts an exponent over any coefficient field.
The remaining whole-local factor is unramified, not necessarily trivial.
-/

@[expose] public noncomputable section
namespace GaloisRepresentation.SerreWeight
open Extensions
variable (p : ℕ) [Fact p.Prime]
local notation "K" =>
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ (LocalCyclotomic.rationalPlace p)
local notation "G" => Field.absoluteGaloisGroup K
local notation "I" => localInertiaGroup (LocalCyclotomic.rationalPlace p)

/-- The mod-p cyclotomic character on the original local absolute Galois group. -/
def localModCyclotomic : G →* (ZMod p)ˣ :=
  (modularCyclotomicCharacter (AlgebraicClosure K)
    (HasEnoughRootsOfUnity.natCard_rootsOfUnity _ p)).comp
      { toFun := fun σ ↦ σ.toRingEquiv
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }

/-- Its restriction is exactly the arithmetic inertia character already constructed. -/
theorem localModCyclotomic_inertia :
    (localModCyclotomic p).comp (I).subtype = LocalCyclotomic.inertiaCharacter p := rfl

variable {k : Type*} [Field k] (f : ZMod p →+* k)
  (χ : Field.absoluteGaloisGroup (IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ
    (LocalCyclotomic.rationalPlace p)) →* kˣ)
  (hker : (LocalCyclotomic.inertiaCharacter p).ker ≤
    (χ.comp (localInertiaGroup (LocalCyclotomic.rationalPlace p)).subtype).ker)

/-- The normalized exponent uses proved arithmetic surjectivity. -/
def localCharacterExponent : ℕ :=
  coefficientCharacterExponent f (LocalCyclotomic.inertiaCharacter p)
    (χ.comp (I).subtype) (LocalCyclotomic.inertiaCharacter_surjective p) hker

/-- Normalization recovers precisely the inertia restriction. -/
theorem localCharacterExponent_spec :
    1 ≤ localCharacterExponent p f χ hker ∧ localCharacterExponent p f χ hker ≤ p - 1 ∧
      ∀ g : I, χ g = Units.map f.toMonoidHom (localModCyclotomic p g) ^
        localCharacterExponent p f χ hker :=
  coefficientCharacterExponent_spec f _ _ _ hker

/-- The whole-local residual factor after removing the normalized cyclotomic power. -/
def localUnramifiedFactor : G →* kˣ :=
  χ / ((Units.map f.toMonoidHom).comp (localModCyclotomic p)) ^
    localCharacterExponent p f χ hker

/-- The extracted factor is trivial on the actual local inertia group. -/
theorem localUnramifiedFactor_unramified :
    CharacterUnramified I (localUnramifiedFactor p f χ hker) := by
  intro g hg
  have he := (localCharacterExponent_spec p f χ hker).2.2 ⟨g, hg⟩
  change χ g / _ = 1
  rw [he]
  exact div_self' _

/-- Reconstruct the whole-local character with its unramified factor retained. -/
theorem localCharacter_factorization :
    χ = localUnramifiedFactor p f χ hker *
      ((Units.map f.toMonoidHom).comp (localModCyclotomic p)) ^
        localCharacterExponent p f χ hker := by
  simp [localUnramifiedFactor]

/-- Inertia exponent one alone leaves a possibly nontrivial unramified factor. -/
theorem localCharacter_eq_cyclotomic_iff :
    χ = (Units.map f.toMonoidHom).comp (localModCyclotomic p) ↔
      localCharacterExponent p f χ hker = 1 ∧ localUnramifiedFactor p f χ hker = 1 := by
  constructor
  · intro he
    have hb : localCharacterExponent p f χ hker = 1 := by
      subst χ
      exact coefficientCharacterExponent_self f _ _ hker
    refine ⟨hb, ?_⟩
    unfold localUnramifiedFactor
    rw [hb, pow_one, he, div_self']
  · rintro ⟨hb, hu⟩
    simpa only [hb, hu, one_mul, pow_one] using localCharacter_factorization p f χ hker

end GaloisRepresentation.SerreWeight
