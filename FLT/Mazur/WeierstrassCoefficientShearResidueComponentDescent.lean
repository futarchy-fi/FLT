/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearSmoothComponentDescent
public import FLT.Mazur.NodeTangentCoefficientCover

/-!
# Descent to the original residue coefficients through the actual tangent cover

The residue tangent cover is faithfully flat. Both finite presentation and
the original-zero component descend to the unsheared residue equation model.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
local notation "K" => ResidueField R
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
local notation "gK" => coefficientShearGluedStructure hπ data K 0 j hj
local notation "gQ" => coefficientShearGluedStructure hπ data Q r j hj
local notation "f" => IsScalarTower.toAlgHom R K Q
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
  [LocallyOfFinitePresentation (coefficientShearGluedStructure hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) j hj)]

/-- Local finite presentation descends to the original, unsplit residue model. -/
theorem coefficientShearResidueStructure_lfp : LocallyOfFinitePresentation gK :=
  coefficientShearSpecialization_lfp hπ data K Q 0 r j hj f
    (nodeTangentAlgebra_faithfullyFlat V)

/-- The identified complete component upstairs descends with the original smooth embedding. -/
theorem coefficientShearResidueOriginalZero_component_descends
    (z : (gQ).smoothLocus.toScheme)
    (hz : (gQ).smoothLocus.ι '' connectedComponent z =
      Set.range (coefficientShearSmoothEmbedding hπ data Q r j hj)) (x : Spec (.of K)) :
    let _ : LocallyOfFinitePresentation gK := coefficientShearResidueStructure_lfp hπ data j hj
    (gK).smoothLocus.ι '' connectedComponent
      (coefficientShearOriginalSmoothZero hπ data K 0 j hj x) =
        Set.range (coefficientShearSmoothEmbedding hπ data K 0 j hj) := by
  let _ : LocallyOfFinitePresentation gK := coefficientShearResidueStructure_lfp hπ data j hj
  exact coefficientShearOriginalZero_component_descends hπ data K Q 0 r j hj f
    (nodeTangentAlgebra_faithfullyFlat V) z hz x

end FLT.Mazur.WeierstrassDividedDepth
