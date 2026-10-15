/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricGroundQuotient
public import FLT.Mazur.GeometricGroundQuotientOriginalComparison
public import FLT.Mazur.VariableHilbertGroundQuotientOpen

/-!
# Affine schemes with open original-quotient image through arbitrary classes

An arbitrary original geometric Picard class constructs an affine scheme
mapping openly to its original invariant quotient. The whole geometric map
and its original coefficient map are retained. The map is not asserted to be
injective or an open immersion; effective descent of its sheaf is still needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] variableChartFixedBaseQuotientMap
  invariantLocallyRingedProjection invariantLocallyRingedBaseMap
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (t : Spec (.of K) ⟶ Spec (.of R))

include hL in
/-- Original classes have affine open-image presentations preserving their entire field maps. -/
theorem exists_arbitrary_geometric_original_open_image
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
      (b : Over.mk t ⟶ A), IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      IsOpenImmersion k.left ∧
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) = s ∧
      ∃ (Q : Scheme)
        (j : Q.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace
          (variableChartEquivalenceRelation f hL d V c))
        (w : Spec (.of K) ⟶ Q), IsAffine Q ∧ IsOpenMap j.base ∧
        w.toLRSHom ≫ j = (b ≫ k).left.toLRSHom ≫
          invariantLocallyRingedProjection (variableChartEquivalenceRelation f hL d V c) ∧
        w.toLRSHom ≫ j ≫
          invariantLocallyRingedBaseMap (variableChartEquivalenceRelation f hL d V c) =
            t.toLRSHom := by
  obtain ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, _,
    S, hS, hZ, a, W, hW, hWe, hWf, hWs, v, ha, hv, z, hz, _, Q, j, w, hQ, hj, hw⟩ :=
    exists_arbitrary_geometric_ground_quotient f hL t s
  let _ := he
  let _ := hv
  let _ := hj
  let J := geometricGroundQuotientComparison f a hL d V W v c
  refine ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, Q, j ≫ J, w, hQ, ?_, ?_, ?_⟩
  · dsimp only [J]
    rw [geometricGroundQuotientComparison]
    exact variableChartFixedBaseQuotientMap_chart_isOpenMap f a hL d V W v c j
  · exact geometric_ground_quotient_original f a hL d V W v c k b z hz j w hw
  · simpa only [Category.assoc] using
      geometric_ground_quotient_original_base f a hL d V W v c k b z hz j w hw

end FLT.Mazur.HilbertChart.AffineRestriction
