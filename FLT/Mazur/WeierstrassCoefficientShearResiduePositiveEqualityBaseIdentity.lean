/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResiduePositiveEqualityOriginalIdentity
public import FLT.Mazur.WeierstrassCoefficientShearResidueComponentDescent

/-!
# The original residue-base component in the PositiveEquality case

The full original smooth orbit is the connected component of the original
zero over the unsplit residue field. Its contraction and embedding are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "K" => ResidueField R
local notation "gK" => coefficientShearGluedStructure hπ data K 0 (s + 1) hs
local notation "BK" => coefficientShearSmoothEmbedding hπ data K 0 (s + 1) hs
local notation "pK" => coefficientShearGluedProjection hπ data K 0 (s + 1) hs

include hm he hstart h3 h4 h6 h6next hc in
/-- The actual unsplit residue equation model is locally of finite presentation. -/
theorem coefficientShearResiduePositiveEqualityBaseStructure_lfp :
    LocallyOfFinitePresentation gK := by
  let _ : LocallyOfFinitePresentation g :=
    coefficientShearResiduePositiveEqualityStructure_lfp
      hπ hm data s hs he hstart h3 h4 h6 h6next hc
  exact coefficientShearResidueStructure_lfp hπ data (s + 1) hs

/-- The entire component at the original residue zero is its independently retained smooth orbit. -/
theorem coefficientShearResiduePositiveEqualityBase_originalZero_component_image
    (x : Spec (.of K)) :
    let _ : LocallyOfFinitePresentation gK :=
      coefficientShearResiduePositiveEqualityBaseStructure_lfp
      hπ hm data s hs he hstart h3 h4 h6 h6next hc
    (gK).smoothLocus.ι '' connectedComponent
      (coefficientShearOriginalSmoothZero hπ data K 0 (s + 1) hs x) = Set.range BK := by
  let _ : LocallyOfFinitePresentation g :=
    coefficientShearResiduePositiveEqualityStructure_lfp
      hπ hm data s hs he hstart h3 h4 h6 h6next hc
  let _ : LocallyOfFinitePresentation gK :=
    coefficientShearResiduePositiveEqualityBaseStructure_lfp
      hπ hm data s hs he hstart h3 h4 h6 h6next hc
  let y : Spec (.of Q) := ⟨⊥, inferInstance⟩
  exact coefficientShearResidueOriginalZero_component_descends hπ data (s + 1) hs
    (coefficientShearOriginalSmoothZero hπ data Q r (s + 1) hs y)
    (coefficientShearResiduePositiveEquality_originalZero_component_image
      hπ hm data s hs he hstart h3 h4 h6 h6next hc y) x

/-- The descended original identity component is the exact original contraction inverse image. -/
theorem coefficientShearResiduePositiveEqualityBase_originalZero_component_contraction
    (x : Spec (.of K)) :
    let _ : LocallyOfFinitePresentation gK :=
      coefficientShearResiduePositiveEqualityBaseStructure_lfp
      hπ hm data s hs he hstart h3 h4 h6 h6next hc
    (gK).smoothLocus.ι '' connectedComponent
      (coefficientShearOriginalSmoothZero hπ data K 0 (s + 1) hs x) =
        (pK ≫ finiteGlobalContraction hπ data (s + 1) hs) ⁻¹'
          (integralSmoothOpen W : Set _) := by
  let _ : LocallyOfFinitePresentation gK :=
    coefficientShearResiduePositiveEqualityBaseStructure_lfp
      hπ hm data s hs he hstart h3 h4 h6 h6next hc
  exact (coefficientShearResiduePositiveEqualityBase_originalZero_component_image
    hπ hm data s hs he hstart h3 h4 h6 h6next hc x).trans
      (coefficientShearSmoothEmbedding_contraction_range hπ data K 0 (s + 1) hs)

end FLT.Mazur.WeierstrassDividedDepth
