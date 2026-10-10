/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EtaleAlgebraReduced
public import FLT.Mazur.EtaleCoordinate
public import Mathlib.RingTheory.Smooth.StandardSmoothOfFree

/-!
# Reducedness of smooth algebras over domains

A standard-smooth presentation gives an étale map from a polynomial ring,
which is a domain. General smooth algebras are covered by standard-smooth
principal localizations, where nilpotents vanish.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.Approximation

universe u v

/-- Standard-smooth algebras over a domain are reduced. -/
theorem isReduced_of_standardSmooth_domain (R : Type u) (B : Type v)
    [CommRing R] [IsDomain R] [CommRing B] [Algebra R B]
    [Algebra.IsStandardSmooth R B] : IsReduced B := by
  obtain ⟨ι, σ, _, _, ⟨P⟩⟩ := Algebra.IsStandardSmooth.out (R := R) (S := B)
  have he := P.freeCoordinateHom_etale
  algebraize [P.freeCoordinateHom.toRingHom]
  exact isReduced_of_etale_domain (MvPolynomial P.FreeCoordinates R) B

/-- Smooth algebras over a domain are reduced, including the zero algebra. -/
theorem isReduced_of_smooth_domain (R : Type u) (B : Type v)
    [CommRing R] [IsDomain R] [CommRing B] [Algebra R B] [Algebra.Smooth R B] :
    IsReduced B := by
  obtain ⟨s, hs, hss⟩ := Algebra.Smooth.exists_span_eq_top_isStandardSmooth R B
  constructor
  intro x hx
  apply Module.eq_zero_of_isLocalized_span s hs
    (fun r : s ↦ Localization.Away r.val) (fun r ↦ Algebra.linearMap B _) x
  intro r
  let _ := hss r.val r.property
  have : IsReduced (Localization.Away r.val) :=
    isReduced_of_standardSmooth_domain R _
  exact (hx.map (algebraMap B (Localization.Away r.val))).eq_zero

end FLT.Mazur.Approximation
