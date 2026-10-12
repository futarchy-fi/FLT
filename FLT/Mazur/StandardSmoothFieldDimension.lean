/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleAffineSpaceDimension
public import FLT.Mazur.EtaleCoordinate

/-!
# Krull dimension of standard smooth algebras over fields

The free coordinates of a submersive presentation give an etale chart.
Consequently its relative dimension is the actual Krull dimension, whenever
the algebra is nonzero.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.FCurve
set_option backward.isDefEq.respectTransparency false

/-- The dimension of a nonzero submersive field algebra counts its free coordinates. -/
theorem submersivePresentation_ringKrullDim {K A ι σ : Type*}
    [Field K] [CommRing A] [Nontrivial A] [Algebra K A] [Finite ι] [Finite σ]
    (P : Algebra.SubmersivePresentation K A ι σ) :
    ringKrullDim A = P.dimension := by
  have he := P.freeCoordinateHom_etale
  algebraize [P.freeCoordinateHom.toRingHom]
  rw [ringKrullDim_eq_card_of_etale_mvPolynomial K A P.FreeCoordinates,
    P.card_freeCoordinates]

/-- Standard smooth relative dimension over a field agrees with Krull dimension. -/
theorem standardSmooth_ringKrullDim (K A : Type*) [Field K] [CommRing A]
    [Nontrivial A] [Algebra K A] (d : ℕ)
    [Algebra.IsStandardSmoothOfRelativeDimension d K A] : ringKrullDim A = d := by
  obtain ⟨ι, σ, _, _, P, hP⟩ :=
    Algebra.IsStandardSmoothOfRelativeDimension.out (n := d) (R := K) (S := A)
  rw [submersivePresentation_ringKrullDim P, hP]

/-- A standard smooth field algebra has some relative dimension detected by its spectrum. -/
theorem standardSmooth_exists_dimension (K A : Type*) [Field K] [CommRing A]
    [Nontrivial A] [Algebra K A] [Algebra.IsStandardSmooth K A] :
    ∃ d : ℕ, Algebra.IsStandardSmoothOfRelativeDimension d K A ∧ ringKrullDim A = d := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := K) (S := A)
  let hd : Algebra.IsStandardSmoothOfRelativeDimension P.dimension K A :=
    ⟨ι, σ, inferInstance, inferInstance, P, rfl⟩
  exact ⟨P.dimension, hd, submersivePresentation_ringKrullDim P⟩

end FLT.Mazur.FCurve
