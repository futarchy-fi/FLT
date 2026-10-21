/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRelationSupport
public import FLT.Mazur.SchemeAdicVanishingOpen

/-!
# The constructed agreement open of an original boundary numerator

The zero-germ locus of the full endpoint discrepancy constructs a canonical
solved arrow open for every raw original numerator. Its equations hold in
the structure sheaf, including nilpotents. Whole-fiber germ equality gives
an actual principal invariant lift when the original scalar map is closed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
open SchemeAdicVanishingNeighborhood InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A}

/-- The full scheme-theoretic endpoint agreement open of a raw original numerator. -/
def originalRelationAgreementOpen (a : Γ(A, ⊤)) : D.Opens :=
  vanishingOpen (p.appTop a - q.appTop a)

/-- Membership tests actual germs rather than values in residue fields. -/
theorem mem_originalRelationAgreementOpen (a : Γ(A, ⊤)) (y : D) :
    y ∈ originalRelationAgreementOpen (p := p) (q := q) a ↔
      D.presheaf.germ ⊤ y (by trivial) (p.appTop a) =
        D.presheaf.germ ⊤ y (by trivial) (q.appTop a) := by
  change D.presheaf.germ ⊤ y _ (p.appTop a - q.appTop a) = 0 ↔ _
  rw [map_sub, sub_eq_zero]

/-- The canonical open solves the full endpoint equation without an additional hypothesis. -/
theorem originalRelationAgreementOpen_equalizes (a : Γ(A, ⊤)) :
    (originalRelationAgreementOpen (p := p) (q := q) a).ι.appTop (p.appTop a) =
      (originalRelationAgreementOpen (p := p) (q := q) a).ι.appTop (q.appTop a) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact vanishingOpen_inclusion_zero _

variable [CompactSpace D] (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤))
  (a : Γ(A, ⊤)) (ha : J.subschemeι.appTop a = t)
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))

include ha in
/-- Every raw lift bounds the original obstruction by its actual nonzero-germ arrow image. -/
theorem originalBoundaryLift_support_subset_discrepancy_image :
    PrimeSpectrum.zeroLocus
        (originalBoundaryLiftIdeal (p := p) (q := q) J t : Set (compatibleFunctions p q)) ⊆
      closure (scalarMorphism σD ''
        (originalRelationAgreementOpen (p := p) (q := q) a : Set D)ᶜ) :=
  originalBoundaryLift_support_subset_relation_image J t a ha _
    (originalRelationAgreementOpen_equalizes a)

/-- Affine original source constructs a raw lift and its canonical discrepancy support bound. -/
theorem exists_originalBoundary_discrepancy_support [IsAffine A] :
    ∃ a : Γ(A, ⊤), J.subschemeι.appTop a = t ∧
      PrimeSpectrum.zeroLocus
          (originalBoundaryLiftIdeal (p := p) (q := q) J t : Set (compatibleFunctions p q)) ⊆
        closure (scalarMorphism σD ''
          (originalRelationAgreementOpen (p := p) (q := q) a : Set D)ᶜ) := by
  obtain ⟨a, ha⟩ := (IsClosedImmersion.isAffine_surjective_of_isAffine J.subschemeι).2 t
  exact ⟨a, ha, originalBoundaryLift_support_subset_discrepancy_image J t a ha⟩

include ha in
/-- Full original-fiber germ equality constructs an actual original principal boundary lift. -/
theorem exists_principalBoundaryLift_of_closed_fiber_germs
    [IsAffine A] [QuasiSeparatedSpace D] (x : PrimeSpectrum (compatibleFunctions p q))
    (hclosed : IsClosedMap (scalarMorphism σD))
    (hx : ∀ y : D, scalarMorphism σD y = x →
      D.presheaf.germ ⊤ y (by trivial) (p.appTop a) =
        D.presheaf.germ ⊤ y (by trivial) (q.appTop a)) :
    ∃ (s : compatibleFunctions p q), s ∉ x.asIdeal ∧
      ∃ u : coefficients p q (A.basicOpen s.val) (compatibleFunctions_basicOpen p q s),
        (J.comap (A.basicOpen s.val).ι).subschemeι.appTop u.val =
          (IdealSheafClosedTransitions.map (J.comap (A.basicOpen s.val).ι) J
            (A.basicOpen s.val).ι rfl).appTop t := by
  apply exists_principalBoundaryLift_of_closed_relation_fiber J t a ha _
    (originalRelationAgreementOpen_equalizes a) x hclosed
  intro y hy
  exact (mem_originalRelationAgreementOpen a y).mpr (hx y hy)

end FLT.Mazur.EquivalenceRelationOrderedFrames
