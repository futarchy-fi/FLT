/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.RootCharacterGenerator
public import FLT.AbsoluteGaloisGroup.RootCharacterUniformizer
public import FLT.GaloisRepresentation.SerreWeight.CyclicCharacterExponent

/-!
# Unique exponents relative to actual root characters

Characters of the constructed finite root quotient have a unique exponent.
It is independent of the uniformizer and its root. The kernel containment
is still a ramification hypothesis, not a classification of representations.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace LocalRoot
open NumberField IsLocalRing GaloisRepresentation.SerreWeight

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "k" => ResidueField (IntegralClosure O Ω)

/-- Every character of the actual finite root quotient has one reduced exponent. -/
theorem existsUnique_rootCharacter_exponent {n : ℕ} (hn : 0 < n)
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1)
    (hnk : (n : k) ≠ 0)
    (χ : localInertiaGroup v →* rootsOfUnity n k)
    (hker : (rootCharacterToRoots v hn hπ hα).ker ≤ χ.ker) :
    ∃! b : ℕ, b < n ∧ ∀ σ, χ σ = rootCharacterToRoots v hn hπ hα σ ^ b := by
  let : NeZero n := ⟨hn.ne'⟩
  let : NeZero (n : k) := ⟨hnk⟩
  let : IsAlgClosed k := residue_isAlgClosed v
  simpa only [HasEnoughRootsOfUnity.natCard_rootsOfUnity] using
    existsUnique_cyclic_character_exponent (rootCharacterToRoots v hn hπ hα) χ
      (rootCharacterToRoots_surjective v hn hπ hα) hker

/-- The finite-quotient normalization itself is independent of uniformizer and root. -/
theorem rootCharacterToRoots_uniformizer_independent {n : ℕ} (hn : 0 < n)
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1)
    {π' : O}
    (hπ' : Valued.v π'.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α' : Ω} (hα' : α' ^ n = algebraMap Kv Ω π'.1) :
    rootCharacterToRoots v hn hπ' hα' = rootCharacterToRoots v hn hπ hα := by
  apply MonoidHom.ext
  intro σ
  apply Subtype.ext
  exact DFunLike.congr_fun (character_uniformizer_independent v hn hπ hπ' hα hα') σ

/-- Two exponents computed from different uniformizers agree in the reduced interval. -/
theorem rootCharacter_exponent_uniformizer_independent {n : ℕ} (hn : 0 < n)
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1)
    (hnk : (n : k) ≠ 0)
    (χ : localInertiaGroup v →* rootsOfUnity n k)
    (hker : (rootCharacterToRoots v hn hπ hα).ker ≤ χ.ker)
    {π' : O} (hπ' : Valued.v π'.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α' : Ω} (hα' : α' ^ n = algebraMap Kv Ω π'.1)
    {a b : ℕ} (ha : a < n) (hb : b < n)
    (hca : ∀ σ, χ σ = rootCharacterToRoots v hn hπ hα σ ^ a)
    (hcb : ∀ σ, χ σ = rootCharacterToRoots v hn hπ' hα' σ ^ b) : a = b := by
  have he := rootCharacterToRoots_uniformizer_independent v hn hπ hα hπ' hα'
  rw [he] at hcb
  exact (existsUnique_rootCharacter_exponent v hn hπ hα hnk χ hker).unique
    ⟨ha, hca⟩ ⟨hb, hcb⟩

end LocalRoot
