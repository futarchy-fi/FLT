/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.GroupScheme.LocalHopfArbitraryCoordinates
public import FLT.GroupScheme.RationalCoordinateRegularPresentation

/-! # Regular local presentations in specified Hopf coordinates -/

@[expose] public noncomputable section

universe u

namespace HopfAlgebra

open MvPolynomial

variable {k A : Type u} [Field k] [CommRing A] [HopfAlgebra k A]
  [IsLocalRing A] [Module.Finite k A]
  (p : ℕ) [Fact p.Prime] [CharP k p] [PerfectRing k p]

include p

/-- Every specified generating tuple has a regular local presentation,
with one equation per coordinate and its original quotient map retained. -/
theorem exists_coordinate_local_regular_presentation {n : ℕ} (x : Fin n → A)
    (hs : Function.Surjective (aeval (R := k) x)) :
    ∃ rs : List (aeval (R := k) x).localizedSource,
      rs.length = n ∧
      RingHom.ker (aeval (R := k) x).localizeAtMaximal = Ideal.ofList rs ∧
      RingTheory.Sequence.IsRegular (aeval (R := k) x).localizedSource rs ∧
      ∃ e : ((aeval (R := k) x).localizedSource ⧸ Ideal.ofList rs) ≃ₐ[k] A,
        ∀ q, e (Ideal.Quotient.mk _ q) = (aeval (R := k) x).localizeAtMaximal q := by
  obtain ⟨r, hr⟩ := exists_relations_of_arbitrary_generators p x hs
  have : IsArtinianRing A := IsArtinianRing.of_finite k A
  exact exists_local_regular_presentation_of_square_kernel
    (Bialgebra.counitAlgHom k A) x hs r hr

end HopfAlgebra
