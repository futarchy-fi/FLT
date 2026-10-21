/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDiscrepancyLocus
public import FLT.Mazur.SchemeFlatScalarSolutionOpen

/-!
# Original invariant boundary lifts from flat branch equations

The numerator and boundary remain on the original source. Only the full arrow
equation is checked after a flat locally finitely presented scalar change.
The common branch solution open and an original scalar denominator are
constructed. Boundary-zero adjustments preserve the literal original boundary.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
open InvariantOpenCoefficientRestriction
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A Y : Scheme.{0}} {p q : D ⟶ A}
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))
variable (g : Y ⟶ Spec (.of (compatibleFunctions p q)))
  [Flat g] [LocallyOfFinitePresentation g] (V : Y.Opens)
local notation "π" => scalarMorphism σD
local notation "k" => pullback.fst π g
local notation "h" => pullback.snd π g
local notation "O" => scalarBranchSolutionOpen σD g V

/-- Full branch equations give the full original endpoint equation on a constructed open. -/
theorem originalRelation_equalizes_on_flat_branch_image (a : Γ(A, ⊤))
    (he : (pullback π g : Scheme).presheaf.map
      (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op
        ((k).appTop (p.appTop a - q.appTop a)) = 0) :
    (O).ι.appTop (p.appTop a) = (O).ι.appTop (q.appTop a) := by
  apply sub_eq_zero.mp
  rw [← map_sub]
  exact scalarBranchSolutionOpen_restrict_zero σD g V _ he

variable [CompactSpace D] [IsAffine A] [QuasiSeparatedSpace D]
  (J : A.IdealSheafData) (t : Γ(J.subscheme, ⊤))

/-- A flat branch equation constructs an invariant principal lift at the original scalar point. -/
theorem exists_principalBoundaryLift_of_flat_relation_branch
    (a : Γ(A, ⊤)) (ha : J.subschemeι.appTop a = t) (y : Y) (hy : y ∈ V)
    (he : (pullback π g : Scheme).presheaf.map
      (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op
        ((k).appTop (p.appTop a - q.appTop a)) = 0) :
    ∃ (s : compatibleFunctions p q), s ∉ (g y).asIdeal ∧
      ∃ u : coefficients p q (A.basicOpen s.val) (compatibleFunctions_basicOpen p q s),
        (J.comap (A.basicOpen s.val).ι).subschemeι.appTop u.val =
          (IdealSheafClosedTransitions.map (J.comap (A.basicOpen s.val).ι) J
            (A.basicOpen s.val).ι rfl).appTop t := by
  obtain ⟨s, hs, hO⟩ := exists_scalar_for_branchSolutionOpen σD g V y hy
  exact ⟨s, hs, exists_principalBoundaryLift_of_relation_open J t a ha O
    (originalRelation_equalizes_on_flat_branch_image g V a he) s hO⟩

/-- Original boundary-zero corrections may be verified solely on the full flat branch. -/
theorem exists_principalBoundaryLift_of_flat_relation_correction
    (a z : Γ(A, ⊤)) (ha : J.subschemeι.appTop a = t)
    (hz : J.subschemeι.appTop z = 0) (y : Y) (hy : y ∈ V)
    (he : (pullback π g : Scheme).presheaf.map
      (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op
        ((k).appTop (p.appTop (a - z) - q.appTop (a - z))) = 0) :
    ∃ (s : compatibleFunctions p q), s ∉ (g y).asIdeal ∧
      ∃ u : coefficients p q (A.basicOpen s.val) (compatibleFunctions_basicOpen p q s),
        (J.comap (A.basicOpen s.val).ι).subschemeι.appTop u.val =
          (IdealSheafClosedTransitions.map (J.comap (A.basicOpen s.val).ι) J
            (A.basicOpen s.val).ι rfl).appTop t := by
  apply exists_principalBoundaryLift_of_flat_relation_branch g V J t (a - z) _ y hy he
  rw [map_sub, ha, hz, sub_zero]

end FLT.Mazur.EquivalenceRelationOrderedFrames
