/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicMarkingOrbitDivisor
public import FLT.Mazur.CartierSectionProductRank

/-!
# Cyclic orbit divisors on possibly singular generalized curves

Every cyclic label contributes its section ideal, even when labels coincide.
Smoothness of the group alone gives a relative Cartier divisor of degree n on
the whole proper curve; no faithful or etale marking is required.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S) {n : ℕ}
  (φ : Multiplicative (ZMod n) →* (𝟙_ (Over S) ⟶ E.group))
  [SmoothOfRelativeDimension 1 E.group.hom]

/-- Repeated cyclic sections remain Cartier on the whole possibly singular curve. -/
theorem cyclicMarkingIdeal_smoothOpen_cartier :
    FCurve.RelativeEffectiveCartier E.curve.hom (E.cyclicMarkingIdeal φ) := by
  have : IsProper E.curve.hom := E.family.family.1
  have : SmoothOfRelativeDimension 1 (E.inclusion.left ≫ E.curve.hom) := by
    rw [E.inclusion.w]
    infer_instance
  exact FCurve.relativeEffectiveCartier_smoothOpen_section_prod E.inclusion.left E.curve.hom
    Finset.univ (fun i : Fin n ↦ (φ (.ofAdd (i.val : ZMod n))).left)
    (fun i _ ↦ by
      rw [← Category.assoc]
      exact (φ (.ofAdd (i.val : ZMod n)) ≫ E.inclusion).w)

/-- The full orbit product has degree n across singular fibers, including label collisions. -/
theorem cyclicMarkingIdeal_smoothOpen_degree :
    FCurve.FiniteLocallyFreeDegree
      ((E.cyclicMarkingIdeal φ).subschemeι ≫ E.curve.hom) n := by
  have : IsProper E.curve.hom := E.family.family.1
  have : LocallyOfFinitePresentation E.curve.hom := E.family.family.2.2
  have : SmoothOfRelativeDimension 1 (E.inclusion.left ≫ E.curve.hom) := by
    rw [E.inclusion.w]
    infer_instance
  simpa only [cyclicMarkingIdeal, Over.comp_left, Finset.card_univ, Fintype.card_fin] using
    FCurve.finiteLocallyFreeDegree_smoothOpen_section_prod E.curve.hom Finset.univ
      E.inclusion.left (fun i : Fin n ↦ (φ (.ofAdd (i.val : ZMod n))).left)
      (fun i ↦ by
        rw [← Category.assoc]
        exact (φ (.ofAdd (i.val : ZMod n)) ≫ E.inclusion).w)

end FLT.Mazur.GeneralizedEllipticCurve
