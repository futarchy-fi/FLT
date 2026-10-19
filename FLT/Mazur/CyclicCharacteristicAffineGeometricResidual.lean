/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualRelabel
public import FLT.Mazur.CyclicCharacteristicComparisonNoetherian
public import FLT.Mazur.SchemeGeometricNilpotentSections

/-!
# Finite fixed functions satisfy the full affine relation modulo nilpotents

The restricted original comparison scheme retains geometric relabeling of its
endpoints. Its Noetherian geometry turns equality on geometric tests into a
nilpotent discrepancy. This does not replace full invariance by finite invariance.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- The entire restricted arrow scheme is Noetherian, including its infinitesimal structure. -/
instance affineResidualDomain_isNoetherian :
    IsNoetherian (affineResidualDomain n i).toScheme where
  toIsLocallyNoetherian := inferInstance
  toCompactSpace := isCompact_iff_compactSpace.mp
    (NoetherianSpace.isCompact (affineResidualDomain n i : Set (productSubgroupScheme n i.1 i.1)))

/-- Geometric endpoints in the selected affine source differ by its original relabeling. -/
theorem affineResidual_geometric_orbit {K : Type} [Field K] [IsAlgClosed K]
    (p : Spec (.of K) ⟶ (affineResidualDomain n i).toScheme) :
    ∃ g : RelabelGroup n, (p ≫ affineResidualSource n i) ≫
      (invariantAffineAction n i g).hom = p ≫ affineResidualTarget n i := by
  obtain ⟨g, hg⟩ := productScheme_geometric_sameChart_orbit n i.1
    (p ≫ (affineResidualDomain n i).ι)
  refine ⟨g, (cancel_mono (invariantAffineInclusion n i)).mp ?_⟩
  calc
    _ = p ≫ affineResidualSource n i ≫ invariantAffineInclusion n i ≫
        (normalizedRelabelAction n i.1 g).hom := by
      rw [Category.assoc, Category.assoc, invariantAffineAction_inclusion]
    _ = (p ≫ (affineResidualDomain n i).ι ≫ productArrowSource n i.1 i.1) ≫
        (normalizedRelabelAction n i.1 g).hom := by
      rw [← Category.assoc (affineResidualSource n i), affineResidualSource_inclusion]
      simp only [Category.assoc]
    _ = p ≫ (affineResidualDomain n i).ι ≫ productArrowTarget n i.1 i.1 := by
      simpa only [Category.assoc] using hg
    _ = _ := by rw [Category.assoc, affineResidualTarget_inclusion]

/-- Finite fixed functions agree on every geometric test of the full residual arrow scheme. -/
theorem affineRelabelSections_geometric_condition (s : affineRelabelSections n i)
    {K : Type} [Field K] [IsAlgClosed K]
    (p : Spec (.of K) ⟶ (affineResidualDomain n i).toScheme) :
    p.appTop ((affineResidualSource n i).appTop s.val) =
      p.appTop ((affineResidualTarget n i).appTop s.val) := by
  obtain ⟨g, hg⟩ := affineResidual_geometric_orbit n i p
  have h := congrArg (fun f => f.appTop s.val) hg
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, s.property g] using h

/-- The obstruction to full residual invariance of a finite fixed function is nilpotent. -/
theorem affineRelabelSections_discrepancy_nilpotent (s : affineRelabelSections n i) :
    IsNilpotent ((affineResidualSource n i).appTop s.val -
      (affineResidualTarget n i).appTop s.val) := by
  apply SchemeGeometricNilpotentSections.isNilpotent_sub_of_geometric_pullback
  intro K _ _ p
  exact affineRelabelSections_geometric_condition n i s p

end FLT.Mazur.CyclicCharacteristicOrbit
