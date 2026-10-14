/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentScaleOneDetection
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneConic
public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroExteriorDetection
public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneHomExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneHomExt
public import FLT.Mazur.WeierstrassCoefficientShearResidueAdjacentLineDetection
public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictConicDetection
public import FLT.Mazur.WeierstrassCoefficientShearRetainedHomExt
import all FLT.Mazur.WeierstrassCoefficientShearRetainedHomExt

/-!
# Complete original components detect the first retained scale-one chart

The exterior and the whole first adjacent pair or strict terminal pair detect the full equation.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (0 + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (0 + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hle" => Nat.le_of_lt hk
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hle h3 h4 hc
local notation "T" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

open WeierstrassModificationX WeierstrassSuccessiveX
variable {Y : Scheme} (u v : coefficientShearGlued hπ data
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R))))
    (AdjoinRoot.root (nodeTangentPolynomial (W.map (residue R)))) (s + 1) hs ⟶ Y)
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d
  (show 2 * (0 + 1) ≤ depth from by omega) h3 h4
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hu" => Eq.mp (congrArg IsUnit ha) (Units.isUnit a)

/-- The first full retained chart is determined even when the original cycle has length three. -/
theorem coefficientShearResidueStrictZeroFirstRetained_hom_ext
    (hF : F ≫ u = F ≫ v) (hB : ∀ j k, B j k ≫ u = B j k ≫ v)
    (hT : ∀ k, T k ≫ u = T k ≫ v) :
    coefficientShearGluedChart hπ data Q r (s + 1) hs (.inr ⟨0, by omega⟩) ≫ u =
      coefficientShearGluedChart hπ data Q r (s + 1) hs (.inr ⟨0, by omega⟩) ≫ v := by
  apply coefficientShearRetainedScaleOne_hom_ext data Q r (s + 1) hs ⟨0, by omega⟩
    (by simp) hp (lin).1 (lin).2 hr hu
  · by_cases hs0 : s = 0
    · subst s
      have H := coefficientShearResidueStrictZeroConic_hom_ext
        hπ hm data 0 hs hk h3 h4 h6 hc rfl u v (hT 0) (hT 1)
      simpa only [coefficientShearRetainedScaleOneConic,
        coefficientShearRetainedTensorChart, coefficientShearRetainedScaleOneTensorIso,
        Category.assoc] using H
    · have H := coefficientShearResidueAdjacentScaleOneConic_hom_ext
        hπ hm data s hs hle h3 h4 hc ⟨0, by omega⟩ rfl u v
          (hB ⟨0, by omega⟩ 0) (hB ⟨0, by omega⟩ 1)
      simpa only [coefficientShearRetainedTensorChart, coefficientShearRetainedScaleOneTensorIso,
        Fin.castSucc, Fin.castAdd, Fin.castLE, Category.assoc] using H
  · simpa only [coefficientShearRetainedTensorChart,
      coefficientShearRetainedScaleOneTensorIso, Category.assoc] using
      coefficientShearResidueZeroIncidence_hom_ext
      hπ hm data s hs hle h3 h4 hc u v hF

end FLT.Mazur.WeierstrassDividedDepth
