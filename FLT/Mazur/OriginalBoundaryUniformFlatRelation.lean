/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryFlatRelationLift
public import FLT.Mazur.OriginalBoundaryUniformRelationIdeal

/-!
# Uniform original ideal powers from a common flat branch

The original open is constructed before choosing any numerator. Noetherianity
of the arrow scheme and finite generation of the specified original ideal give
one power for every boundary-zero correction satisfying the full branch
equations. No finiteness of the full correction quotient is inferred.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open SchemeEffectiveEpiSections SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A Y : Scheme.{0}} {p q : D ⟶ A} [IsNoetherian D]
local notation "σD" => p.appTop.hom.comp (Subring.subtype (compatibleFunctions p q))
variable (g : Y ⟶ Spec (.of (compatibleFunctions p q)))
  [Flat g] [LocallyOfFinitePresentation g] (V : Y.Opens)
local notation "π" => scalarMorphism σD
local notation "k" => pullback.fst π g
local notation "h" => pullback.snd π g
local notation "O" => scalarBranchSolutionOpen σD g V

/-- One original ideal power works before any raw boundary or numerator is chosen. -/
theorem exists_pow_le_originalBoundaryLiftIdeals_of_flat_branch
    (Q : Ideal (compatibleFunctions p q)) (hfg : Q.FG)
    (hQ : Q ≤ scalarAvoidanceIdeal σD O) :
    ∃ N : ℕ, ∀ (J : A.IdealSheafData) (a : Γ(A, ⊤)),
      (pullback π g : Scheme).presheaf.map
        (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op
          ((k).appTop (p.appTop a - q.appTop a)) = 0 →
      Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J (J.subschemeι.appTop a) := by
  obtain ⟨N, hN⟩ := exists_pow_le_originalRelationMultiplierIdeal O Q hfg hQ
  refine ⟨N, fun J a ha s hs ↦ ?_⟩
  exact originalRelationMultiplier_mem_liftIdeal O s (hN hs) J a
    (originalRelation_equalizes_on_flat_branch_image g V a ha)

/-- The same power works for arbitrary original boundary-zero changes, chosen afterwards. -/
theorem exists_pow_le_originalBoundaryLiftIdeals_of_flat_corrections
    (Q : Ideal (compatibleFunctions p q)) (hfg : Q.FG)
    (hQ : Q ≤ scalarAvoidanceIdeal σD O) :
    ∃ N : ℕ, ∀ (J : A.IdealSheafData) (a z : Γ(A, ⊤)),
      J.subschemeι.appTop z = 0 →
      (pullback π g : Scheme).presheaf.map
        (homOfLE le_top : h ⁻¹ᵁ V ⟶ ⊤).op
          ((k).appTop (p.appTop (a - z) - q.appTop (a - z))) = 0 →
      Q ^ N ≤ originalBoundaryLiftIdeal (p := p) (q := q) J (J.subschemeι.appTop a) := by
  obtain ⟨N, hN⟩ := exists_pow_le_originalBoundaryLiftIdeals_of_flat_branch g V Q hfg hQ
  refine ⟨N, fun J a z hz he ↦ ?_⟩
  simpa only [map_sub, hz, sub_zero] using hN J (a - z) he

end FLT.Mazur.EquivalenceRelationOrderedFrames
