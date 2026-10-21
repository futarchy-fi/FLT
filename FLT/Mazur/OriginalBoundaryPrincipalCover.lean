/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryPrincipalLiftCriterion

/-!
# Constructing principal boundary lifts from original scalar covers

Local full-boundary lifts need not agree on overlaps. Their original lift
multipliers form an ideal, so a cover in the original scalar spectrum
constructs a new lift on the entire requested principal neighborhood.
The cover is not replaced by a cover of source points or individual fibers.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsAffine A]
  [CompactSpace D] [QuasiSeparatedSpace D] (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤))
  {ι : Type*} (s : ι → compatibleFunctions p q)
  (hs : ∀ i, ∃ u : coefficients p q (A.basicOpen (s i).val)
      (compatibleFunctions_basicOpen p q (s i)),
    (J.comap (A.basicOpen (s i).val).ι).subschemeι.appTop u.val =
      (IdealSheafClosedTransitions.map (J.comap (A.basicOpen (s i).val).ι) J
        (A.basicOpen (s i).val).ι rfl).appTop t)

include hs in
/-- Arbitrary original scalar covers construct new principal lifts without matching local values. -/
theorem exists_principalBoundaryLift_of_scalar_cover (r : compatibleFunctions p q)
    (hcover : (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum (compatibleFunctions p q))) ⊆
      ⋃ i, (PrimeSpectrum.basicOpen (s i) : Set (PrimeSpectrum (compatibleFunctions p q)))) :
    ∃ u : coefficients p q (A.basicOpen r.val) (compatibleFunctions_basicOpen p q r),
      (J.comap (A.basicOpen r.val).ι).subschemeι.appTop u.val =
        (IdealSheafClosedTransitions.map (J.comap (A.basicOpen r.val).ι) J
          (A.basicOpen r.val).ι rfl).appTop t := by
  apply (mem_originalBoundaryLiftIdeal_radical_iff_principal r J t).mp
  rw [← PrimeSpectrum.vanishingIdeal_zeroLocus_eq_radical, PrimeSpectrum.mem_vanishingIdeal]
  intro x hx
  by_contra hr
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hcover hr)
  have hsi := (mem_originalBoundaryLiftIdeal_radical_iff_principal (s i) J t).mpr (hs i)
  exact hi ((x.isPrime.radical_le_iff.mpr hx) hsi)

include hs in
/-- An original scalar principal cover of the whole spectrum constructs an unscaled global lift. -/
theorem exists_originalBoundaryLift_of_scalar_cover
    (hcover : (⋃ i, (PrimeSpectrum.basicOpen (s i) :
      Set (PrimeSpectrum (compatibleFunctions p q)))) = Set.univ) :
    ∃ w : compatibleFunctions p q, J.subschemeι.appTop w.val = t := by
  have hr : (1 : compatibleFunctions p q) ∈
      (originalBoundaryLiftIdeal (p := p) (q := q) J t).radical := by
    apply (mem_originalBoundaryLiftIdeal_radical_iff_principal 1 J t).mpr
    apply exists_principalBoundaryLift_of_scalar_cover J t s hs 1
    rw [hcover]
    exact Set.subset_univ _
  obtain ⟨N, hN⟩ := hr
  apply (one_mem_originalBoundaryLiftIdeal J t).mp
  simpa only [one_pow] using hN

end FLT.Mazur.EquivalenceRelationOrderedFrames
