/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.AbsoluteGaloisGroup.FundamentalTame
public import FLT.AbsoluteGaloisGroup.RootCharacterResidue
public import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed

/-!
# Generators of original reduced root characters

Choose the inertia element from the full root-character image before taking
any norm. The order is proved using residue roots of unity and surjectivity.
-/

@[expose] public noncomputable section
namespace LocalRoot
open NumberField IsLocalRing

variable {K : Type*} [Field K] [NumberField K]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
local notation "Kv" => v.adicCompletion K
local notation "O" => v.adicCompletionIntegers K
local notation "Ω" => AlgebraicClosure Kv
local notation "k" => ResidueField (IntegralClosure O Ω)

/-- A prime-to-characteristic uniformizer-root character attains its full order. -/
theorem exists_rootCharacter_generator {n : ℕ} (hn : 0 < n) (hnk : (n : k) ≠ 0)
    {π : O} (hπ : Valued.v π.1 = Multiplicative.ofAdd (-1 : ℤ))
    {α : Ω} (hα : α ^ n = algebraMap Kv Ω π.1) :
    ∃ σ : localInertiaGroup v, orderOf (character v hn
      (fun h ↦ IsDedekindDomain.HeightOneSpectrum.adicCompletion.uniformizer_ne_zero
        hπ (Subtype.ext h)) hα σ) = n := by
  let : NeZero n := ⟨hn.ne'⟩
  let : NeZero (n : k) := ⟨hnk⟩
  let : IsAlgClosed k := residue_isAlgClosed v
  obtain ⟨u, hu⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := rootsOfUnity n k)
  obtain ⟨σ, hσ⟩ := rootCharacterToRoots_surjective v hn hπ hα u
  refine ⟨σ, ?_⟩
  have hv := congrArg (fun x : rootsOfUnity n k ↦ x.1) hσ
  change character v hn _ hα σ = u.1 at hv
  rw [hv, Subgroup.orderOf_coe, hu, HasEnoughRootsOfUnity.natCard_rootsOfUnity]

end LocalRoot
