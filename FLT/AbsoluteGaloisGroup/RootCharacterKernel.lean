/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.InertiaCyclicQuotient
public import FLT.AbsoluteGaloisGroup.RootCharacterExponent
public import FLT.AbsoluteGaloisGroup.RootCharacterTopology
public import FLT.GaloisRepresentation.SerreWeight.CyclicPairKernel

/-!
# The universal kernel of a prime-to-p root character

Combine an arbitrary open-kernel root-valued inertia character with the
surjective uniformizer-root character. Their finite joint image is cyclic,
which proves kernel containment. No common-level power cancellation is used.
-/

@[expose] public noncomputable section
namespace LocalRoot
open NumberField IsLocalRing GaloisRepresentation.SerreWeight

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "k" => ResidueField (IntegralClosure O Ω)

/-- Every open-kernel degree-n inertia character kills the degree-n root kernel. -/
theorem rootCharacter_ker_le_of_isOpen {p n : ℕ} (hp : p.Prime)
    [CharP (ResidueField O) p] (hn : 0 < n) (hpn : p.Coprime n)
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1)
    (χ : localInertiaGroup v →* rootsOfUnity n k)
    (hχ : IsOpen (χ.ker : Set (localInertiaGroup v))) :
    (rootCharacterToRoots v hn hπ hα).ker ≤ χ.ker := by
  let : NeZero n := ⟨hn.ne'⟩
  let : CharP k p := charP_of_injective_ringHom
    (ResidueField.map (algebraMap O (IntegralClosure O Ω))).injective p
  let : NeZero (n : k) := ⟨by
    rw [Ne, CharP.cast_eq_zero_iff k p]
    exact hp.coprime_iff_not_dvd.mp hpn⟩
  let : IsAlgClosed k := residue_isAlgClosed v
  let θ := rootCharacterToRoots v hn hπ hα
  have ht : IsOpen (θ.ker : Set (localInertiaGroup v)) := by
    dsimp only [θ, rootCharacterToRoots]
    rw [MonoidHom.ker_codRestrict]
    exact character_ker_isOpen v hn _ hα
  have hc : p.Coprime (Nat.card (rootsOfUnity n k × rootsOfUnity n k)) := by
    rw [Nat.card_prod, HasEnoughRootsOfUnity.natCard_rootsOfUnity]
    exact hpn.mul_right hpn
  let : IsCyclic (θ.prod χ).range :=
    LocalRamification.isCyclic_inertia_range_of_coprime v hp (θ.prod χ)
      (by simpa only [MonoidHom.ker_prod, Subgroup.coe_inf] using ht.inter hχ) hc
  exact ker_le_of_cyclic_pair θ χ (rootCharacterToRoots_surjective v hn hπ hα)

/-- The reduced exponent is now extracted from an open kernel, without a kernel premise. -/
theorem existsUnique_rootCharacter_exponent_of_isOpen {p n : ℕ} (hp : p.Prime)
    [CharP (ResidueField O) p] (hn : 0 < n) (hpn : p.Coprime n)
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1)
    (hnk : (n : k) ≠ 0) (χ : localInertiaGroup v →* rootsOfUnity n k)
    (hχ : IsOpen (χ.ker : Set (localInertiaGroup v))) :
    ∃! b : ℕ, b < n ∧ ∀ σ, χ σ = rootCharacterToRoots v hn hπ hα σ ^ b :=
  existsUnique_rootCharacter_exponent v hn hπ hα hnk χ
    (rootCharacter_ker_le_of_isOpen v hp hn hpn hπ hα χ hχ)

end LocalRoot
