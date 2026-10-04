/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.FiniteHopfComponentTranslation
public import FLT.GroupScheme.LocalHopfRationalRegularPresentation

/-! # Regular local presentations of all geometric Hopf factors -/

@[expose] public noncomputable section

universe u

namespace HopfAlgebra

open FiniteAlgebra MvPolynomial

variable {k A : Type u} [Field k] [IsAlgClosed k] [CommRing A] [HopfAlgebra k A]
  [IsArtinianRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p]

include p

/-- Translation transfers the identity factor's regular presentation to every local factor. -/
theorem exists_component_regular_presentation (m : ComponentIndex A) :
    ∃ (n : ℕ) (rs : List (Localization.AtPrime (rationalPointIdeal (fun _ : Fin n ↦ (0 : k))))),
      rs.length = n ∧
      RingTheory.Sequence.IsRegular
        (Localization.AtPrime (rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))) rs ∧
      Nonempty (((Localization.AtPrime (rationalPointIdeal (fun _ : Fin n ↦ (0 : k)))) ⧸
        Ideal.ofList rs) ≃ₐ[k] Component A m) := by
  obtain ⟨E⟩ := nonempty_componentEquiv_identity (k := k) m
  obtain ⟨n, rs, hlen, hreg, ⟨e⟩⟩ :=
    exists_rational_local_regular_presentation (k := k) (A := FiniteIdentityComponent k A) p
  exact ⟨n, rs, hlen, hreg, ⟨e.trans E.symm⟩⟩

end HopfAlgebra
