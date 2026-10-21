/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDiscrepancyLocus

/-!
# Original principal lifts from all-order full-relation equations

An original numerator whose full endpoint discrepancy lies in every power
of an arrow ideal agrees on a genuine open containing that ideal's entire
support. Closedness of the original scalar map and containment of its whole
fiber then construct an invariant principal boundary lift. The numerator is
one actual original section, not a family of unalgebraized formal sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
open SchemeAdicVanishingNeighborhood InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsLocallyNoetherian D]
  (I : D.IdealSheafData) (a : Γ(A, ⊤))
  (hadic : ∀ (V : D.affineOpens) (n : ℕ),
    D.presheaf.map (homOfLE le_top : V.1 ⟶ ⊤).op (p.appTop a - q.appTop a) ∈
      I.ideal V ^ (n + 1))

include hadic in
/-- All-order full discrepancy equations place the whole arrow support in the constructed open. -/
theorem support_subset_originalRelationAgreementOpen :
    (I.support : Set D) ⊆ originalRelationAgreementOpen (p := p) (q := q) a :=
  support_subset_vanishingOpen (p.appTop a - q.appTop a) I hadic

variable [CompactSpace D] [IsAffine A]
  (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤)) (ha : J.subschemeι.appTop a = t)
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))

include hadic ha in
/-- Adic equations construct a principal invariant lift at a whole supported original fiber. -/
theorem exists_principalBoundaryLift_of_adic_relation_fiber
    (x : PrimeSpectrum (compatibleFunctions p q))
    (hclosed : IsClosedMap (scalarMorphism σD))
    (hx : ∀ y : D, scalarMorphism σD y = x → y ∈ I.support) :
    ∃ (s : compatibleFunctions p q), s ∉ x.asIdeal ∧
      ∃ u : coefficients p q (A.basicOpen s.val) (compatibleFunctions_basicOpen p q s),
        (J.comap (A.basicOpen s.val).ι).subschemeι.appTop u.val =
          (IdealSheafClosedTransitions.map (J.comap (A.basicOpen s.val).ι) J
            (A.basicOpen s.val).ι rfl).appTop t := by
  apply exists_principalBoundaryLift_of_closed_relation_fiber J t a ha _
    (originalRelationAgreementOpen_equalizes a) x hclosed
  intro y hy
  exact support_subset_originalRelationAgreementOpen I a hadic (hx y hy)

end FLT.Mazur.EquivalenceRelationOrderedFrames
