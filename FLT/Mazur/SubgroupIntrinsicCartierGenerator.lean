/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFlatIdealSheafEquality
public import FLT.Mazur.ClosedOrbitKernel
public import FLT.Mazur.CartierSectionProductRank
public import FLT.Mazur.GeneralizedCurveCyclicSubgroup

/-!
# Cartier generators from intrinsic orbit vanishing

On a finite subgroup of a generalized curve, a torsion section with zero
intrinsic orbit product generates the entire ambient subgroup divisor. The
smooth group locus supplies Cartier sections even when the curve is singular.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj

namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup

set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} {E : GeneralizedEllipticCurve S} {n : ℕ}
  (H : E.FiniteSubgroup n) [SmoothOfRelativeDimension 1 E.group.hom]
  (P : 𝟙_ (Over S) ⟶ H.carrier)

/-- Each full orbit section is relative Cartier in the original, possibly singular curve. -/
theorem orbit_section_relativeCartier (k : ℕ) :
    FCurve.RelativeEffectiveCartier E.curve.hom ((P ^ k) ≫ H.curveMap).left.ker := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : SmoothOfRelativeDimension 1 (E.inclusion.left ≫ E.curve.hom) := by
    rw [Over.w]
    infer_instance
  have h := FCurve.smoothOpenSectionCartier E.inclusion.left E.curve.hom
    ((P ^ k) ≫ H.inclusion).left inferInstance inferInstance inferInstance
    (by rw [← Category.assoc]; exact Over.w (((P ^ k) ≫ H.inclusion) ≫ E.inclusion))
  simpa only [curveMap, Over.comp_left, Category.assoc] using h

/-- The full orbit product has the same degree as the original finite subgroup. -/
theorem orbit_product_degree : FCurve.FiniteLocallyFreeDegree
    ((∏ k : Fin n, ((P ^ k.val) ≫ H.curveMap).left.ker).subschemeι ≫ E.curve.hom) n := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : LocallyOfFinitePresentation E.curve.hom := E.family.family.2.2
  have h := FCurve.finiteLocallyFreeDegree_cartier_section_prod E.curve.hom
    (Finset.univ : Finset (Fin n)) (fun k ↦ ((P ^ k.val) ≫ H.curveMap).left)
    (fun k ↦ Over.w _) (fun k ↦ H.orbit_section_relativeCartier P k.val)
  simpa only [Finset.card_univ, Fintype.card_fin] using h

/-- Intrinsic orbit vanishing identifies the whole subgroup ideal, including multiplicities. -/
theorem ideal_eq_orbit_product [IsAffine S]
    (hP : ∏ k : Fin n, (P ^ k.val).left.ker = ⊥) :
    H.ideal = ∏ k : Fin n, ((P ^ k.val) ≫ H.curveMap).left.ker := by
  let _ : IsProper E.curve.hom := E.family.family.1
  let _ : ∀ k : Fin n, IsClosedImmersion ((P ^ k.val).left ≫ H.curveMap.left) := fun k ↦
    FCurve.isClosedImmersion_section E.curve.hom
      ((P ^ k.val) ≫ H.curveMap).left (Over.w _)
  exact (FCurve.idealSheaf_eq_of_le_of_finiteLocallyFreeDegree E.curve.hom _ _
    (ClosedOrbitKernel.orbit_le_ker H.curveMap.left Finset.univ _ hP) n
    (H.orbit_product_degree P) H.ideal_degree).symm

/-- Intrinsic vanishing and torsion give an actual Cartier generator over an affine base. -/
theorem isCartierGenerator_of_intrinsic_orbit [IsAffine S] (ht : P ^ n = 1)
    (hP : ∏ k : Fin n, (P ^ k.val).left.ker = ⊥) : H.IsCartierGenerator P := by
  have he := H.ideal_eq_orbit_product P hP
  refine ⟨ht, ?_, he⟩
  rw [he]
  exact FCurve.relativeEffectiveCartier_prod E.curve.hom Finset.univ _
    (fun k _ ↦ H.orbit_section_relativeCartier P k.val)

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
