/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeCyclicSubgroup

/-!
# Cartier generators on singular generalized curves

For a faithful cyclic marking, the subgroup orbit is relative Cartier whenever
the smooth group has relative dimension one. The entire proper curve need not
be smooth; this applies in particular to the one-gon boundary.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
open UniversallyDistinctSections FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ} [NeZero n]
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  (hφ : UniversallyDistinct (fun i : ZMod n ↦ φ (.ofAdd i)))
  [SmoothOfRelativeDimension 1 E.group.hom]
local notation "H" => E.relativeCyclicSubgroup φ hφ
local notation "P" => E.relativeCyclicGenerator φ hφ

/-- Smoothness of the group alone makes the actual subgroup orbit relative Cartier. -/
theorem relativeCyclicSubgroup_smoothOpen_cartier :
    RelativeEffectiveCartier E.curve.hom (H).ideal := by
  have : IsProper E.curve.hom := E.family.family.1
  have : SmoothOfRelativeDimension 1 (E.inclusion.left ≫ E.curve.hom) := by
    rw [E.inclusion.w]
    infer_instance
  rw [relativeCyclicSubgroup_ideal]
  exact relativeEffectiveCartier_smoothOpen_section_prod E.inclusion.left E.curve.hom
    Finset.univ (fun i : Fin n ↦ ((P ^ i.val) ≫ (H).inclusion).left)
    (fun i _ ↦ ((P ^ i.val) ≫ (H).curveMap).w)

/-- The actual generator is Cartier on the whole curve, including its singular fibers. -/
theorem relativeCyclicGenerator_smoothOpen_cartier : (H).IsCartierGenerator P := by
  refine ⟨?_, E.relativeCyclicSubgroup_smoothOpen_cartier φ hφ,
    E.relativeCyclicSubgroup_ideal φ hφ⟩
  change ConstantCyclicGroup.component S n 1 ^ n = 1
  rw [← ConstantCyclicGenerator.component_natCast, ZMod.natCast_self,
    ConstantCyclicGenerator.component_zero]

/-- The original faithful marking gives a cyclic subgroup across the singular boundary. -/
theorem relativeCyclicSubgroup_smoothOpen_isCyclic : (H).IsCyclic :=
  (E.relativeCyclicGenerator_smoothOpen_cartier φ hφ).isCyclic H

end FLT.Mazur.GeneralizedEllipticCurve
