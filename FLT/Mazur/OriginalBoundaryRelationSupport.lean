/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRelationOpenLift
public import FLT.Mazur.SchemeScalarAvoidanceIdeal

/-!
# Boundary obstruction support from the actual relation equations

A raw original numerator supplies a new support bound: the closed image of
those full relation arrows outside an open on which its endpoints agree.
Avoiding this image constructs an actual principal invariant boundary lift.
The scalar ring and the original prime are unchanged throughout.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
open InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [CompactSpace D]
  (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤))
  (a : Γ(A, ⊤)) (ha : J.subschemeι.appTop a = t)
  (O : D.Opens) (he : O.ι.appTop (p.appTop a) = O.ι.appTop (q.appTop a))
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))

include ha he in
/-- Full arrow equations give an original scalar ideal contained in the exact lift radical. -/
theorem relationAvoidanceIdeal_le_originalBoundaryLiftIdeal_radical :
    scalarAvoidanceIdeal σD O ≤
      (originalBoundaryLiftIdeal (p := p) (q := q) J t).radical := by
  intro s hs
  exact exists_pow_mem_originalBoundaryLiftIdeal_of_relation_open J t a ha O he s
    ((mem_scalarAvoidanceIdeal_iff σD O s).mp hs)

include ha he in
/-- Failure of original lifting lies in the closure of the unsolved full relation image. -/
theorem originalBoundaryLift_support_subset_relation_image :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t : Set (compatibleFunctions p q)) ⊆
      closure (scalarMorphism σD '' (O : Set D)ᶜ) := by
  rw [← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
  intro x hx
  exact (relationAvoidanceIdeal_le_originalBoundaryLiftIdeal_radical J t a ha O he).trans
    (x.isPrime.radical_le_iff.mpr hx)

variable [IsAffine A] [QuasiSeparatedSpace D]

include ha he in
/-- An original prime off the bad arrow image has a constructed invariant principal lift. -/
theorem exists_principalBoundaryLift_off_relation_image
    (x : PrimeSpectrum (compatibleFunctions p q))
    (hx : x ∉ closure (scalarMorphism σD '' (O : Set D)ᶜ)) :
    ∃ (s : compatibleFunctions p q), s ∉ x.asIdeal ∧
      ∃ u : coefficients p q (A.basicOpen s.val) (compatibleFunctions_basicOpen p q s),
        (J.comap (A.basicOpen s.val).ι).subschemeι.appTop u.val =
          (IdealSheafClosedTransitions.map (J.comap (A.basicOpen s.val).ι) J
            (A.basicOpen s.val).ι rfl).appTop t := by
  obtain ⟨s, hs, hO⟩ := (mem_scalarNeighborhoodLocus_iff σD O x).mp hx
  exact ⟨s, hs, exists_principalBoundaryLift_of_relation_open J t a ha O he s hO⟩

include ha he in
/-- For a closed scalar map, solving every arrow over the prime suffices for a principal lift. -/
theorem exists_principalBoundaryLift_of_closed_relation_fiber
    (x : PrimeSpectrum (compatibleFunctions p q))
    (hclosed : IsClosedMap (scalarMorphism σD))
    (hx : ∀ y : D, scalarMorphism σD y = x → y ∈ O) :
    ∃ (s : compatibleFunctions p q), s ∉ x.asIdeal ∧
      ∃ u : coefficients p q (A.basicOpen s.val) (compatibleFunctions_basicOpen p q s),
        (J.comap (A.basicOpen s.val).ι).subschemeι.appTop u.val =
          (IdealSheafClosedTransitions.map (J.comap (A.basicOpen s.val).ι) J
            (A.basicOpen s.val).ι rfl).appTop t := by
  obtain ⟨s, hs, hO⟩ := exists_scalar_of_closed_fiber σD O x hclosed hx
  exact ⟨s, hs, exists_principalBoundaryLift_of_relation_open J t a ha O he s hO⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
