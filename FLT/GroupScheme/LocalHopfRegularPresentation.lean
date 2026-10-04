/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.AugmentedPolynomialLocalParameters
public import FLT.GroupScheme.LocalHopfLocalizedPresentation

/-! # The minimal square local Hopf presentation is a regular presentation -/

@[expose] public noncomputable section

universe u

namespace HopfAlgebra

open MvPolynomial

variable {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]
  [IsLocalRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

include p

/-- The minimal local presentation has a regular sequence of defining equations. -/
theorem exists_minimal_local_regular_presentation :
    ∃ P : Algebra.Generators k A
        (Fin (Module.finrank k (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent)),
      (∀ i, Bialgebra.counitAlgHom k A (P.val i) = 0) ∧
      let f := aeval (R := k) P.val
      ∃ r : Fin (Module.finrank k
          (RingHom.ker (Bialgebra.counitAlgHom k A)).Cotangent) → f.localizedSource,
        Nonempty ((f.localizedSource ⧸ Ideal.span (Set.range r)) ≃ₐ[k] A) ∧
        RingTheory.Sequence.IsRegular f.localizedSource ((List.finRange _).map r) := by
  obtain ⟨P, hx, r, ⟨e⟩⟩ := exists_minimal_local_quotient_presentation (k := k) (A := A) p
  refine ⟨P, hx, r, ⟨e⟩, ?_⟩
  have hspan : Ideal.ofList ((List.finRange _).map r) = Ideal.span (Set.range r) := by
    exact congrArg Ideal.span (Set.ext fun f ↦ by simp)
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  have : IsArtinianRing ((aeval (R := k) P.val).localizedSource ⧸
      Ideal.ofList ((List.finRange _).map r)) := by
    rw [hspan]
    exact e.symm.toRingEquiv.isArtinianRing
  have : Nontrivial ((aeval (R := k) P.val).localizedSource ⧸
      Ideal.ofList ((List.finRange _).map r)) := by
    rw [hspan]
    exact e.surjective.nontrivial
  exact isRegular_localized_augmentation_parameters (Bialgebra.counitAlgHom k A)
    P.val hx _ (by simp)

end HopfAlgebra
