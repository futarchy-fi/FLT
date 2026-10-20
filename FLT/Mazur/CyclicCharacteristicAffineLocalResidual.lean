/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicAffineResidualRelabel
public import FLT.Mazur.CyclicCharacteristicLocalArrowOrbit

/-!
# Exact local orbits in the invariant affine chart

Cancel the original open inclusion after restricting a full same-chart arrow.
Finite fixed functions then have exactly equal pullbacks on each neighborhood.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TopologicalSpace
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] (i : InvariantAffineIndex n)

/-- Full affine residual arrows have exact local orbits in the original affine action. -/
theorem affineResidual_local_orbit {T : Scheme}
    (p : T ⟶ (affineResidualDomain n i).toScheme)
    (hn : IsUnit (n : Γ(T, ⊤))) (x : T) :
    ∃ (g : RelabelGroup n) (U : T.Opens), IsAffineOpen U ∧ x ∈ U ∧
      (U.ι ≫ p ≫ affineResidualSource n i) ≫ (invariantAffineAction n i g).hom =
        U.ι ≫ p ≫ affineResidualTarget n i := by
  obtain ⟨g, U, hU, hx, hg⟩ := productScheme_local_sameChart_orbit n i.1
    (p ≫ (affineResidualDomain n i).ι) hn x
  refine ⟨g, U, hU, hx, (cancel_mono (invariantAffineInclusion n i)).mp ?_⟩
  calc
    _ = U.ι ≫ p ≫ affineResidualSource n i ≫ invariantAffineInclusion n i ≫
        (normalizedRelabelAction n i.1 g).hom := by
      simp only [Category.assoc, invariantAffineAction_inclusion]
    _ = (U.ι ≫ p ≫ (affineResidualDomain n i).ι ≫ productArrowSource n i.1 i.1) ≫
        (normalizedRelabelAction n i.1 g).hom := by
      simp only [Category.assoc, ← affineResidualSource_inclusion]
    _ = U.ι ≫ p ≫ (affineResidualDomain n i).ι ≫ productArrowTarget n i.1 i.1 := by
      simpa only [Category.assoc] using hg
    _ = _ := by simp only [Category.assoc, affineResidualTarget_inclusion]

/-- A fixed function has exactly equal endpoint pullbacks on each local affine orbit. -/
theorem affineRelabelSections_local_condition (s : affineRelabelSections n i)
    {T : Scheme} (p : T ⟶ (affineResidualDomain n i).toScheme)
    (hn : IsUnit (n : Γ(T, ⊤))) (x : T) :
    ∃ U : T.Opens, IsAffineOpen U ∧ x ∈ U ∧
      U.ι.appTop (p.appTop ((affineResidualSource n i).appTop s.val)) =
        U.ι.appTop (p.appTop ((affineResidualTarget n i).appTop s.val)) := by
  obtain ⟨g, U, hU, hx, hg⟩ := affineResidual_local_orbit n i p hn x
  refine ⟨U, hU, hx, ?_⟩
  have h := congrArg (fun f => f.appTop s.val) hg
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply, s.property g] using h

end FLT.Mazur.CyclicCharacteristicOrbit
