/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Deformations.RepresentationTheory.FlatReduction

/-!
# Checking flatness on cofinal coefficient ideals

Models on a cofinal family of open ideals suffice for all open reductions.
For integral lifting, this allows torsion models modulo powers of `p` to be
used once openness and cofinality of those powers have been established.
-/

@[expose] public section

open NumberField

universe u

namespace GaloisRep

variable {K M : Type u} {A : Type} [Field K] [NumberField K]
  [CommRing A] [TopologicalSpace A] [IsTopologicalRing A] [IsLocalRing A]
  [AddCommGroup M] [Module A M] [Module.Free A M] [Module.Finite A M]
  (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (ρ : GaloisRep K A M)

/-- Flatness can be checked on any family cofinal among the open coefficient ideals. -/
theorem isFlatAt_iff_of_cofinal {ι : Type*} (J : ι → Ideal A)
    (hopen : ∀ i, IsOpen (J i : Set A))
    (hcofinal : ∀ I : Ideal A, IsOpen (I : Set A) → ∃ i, J i ≤ I) :
    ρ.IsFlatAt v ↔ ∀ i, (ρ.baseChange (A ⧸ J i)).HasFlatProlongationAt v := by
  constructor
  · exact fun hρ i ↦ hρ.cond (J i) (hopen i)
  · intro hJ
    constructor
    intro I hI
    obtain ⟨i, hi⟩ := hcofinal I hI
    exact hasFlatProlongationAt_quotient_of_le v ρ hi (hJ i)

/-- If powers of `p` give a basis of open coefficient ideals, their finite-flat
models suffice. The topological basis hypotheses are explicit. -/
theorem isFlatAt_iff_of_cofinal_powers (p : ℕ)
    (hopen : ∀ n : ℕ, IsOpen (Ideal.span {(p : A) ^ n} : Set A))
    (hcofinal : ∀ I : Ideal A, IsOpen (I : Set A) →
      ∃ n : ℕ, Ideal.span {(p : A) ^ n} ≤ I) :
    ρ.IsFlatAt v ↔ ∀ n : ℕ,
      (ρ.baseChange (A ⧸ Ideal.span {(p : A) ^ n})).HasFlatProlongationAt v :=
  isFlatAt_iff_of_cofinal v ρ (fun n : ℕ ↦ Ideal.span {(p : A) ^ n}) hopen hcofinal

end GaloisRep
