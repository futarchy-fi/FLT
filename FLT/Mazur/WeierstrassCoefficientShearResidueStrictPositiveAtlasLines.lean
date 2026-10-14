/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps
public import FLT.Mazur.WeierstrassCoefficientShearRetainedTensorLineComparison
import all FLT.Mazur.WeierstrassCoefficientShearResidueStrictPositiveAtlasMaps
import all FLT.Mazur.WeierstrassCoefficientShearResidueTerminalDescent
import all FLT.Mazur.WeierstrassCoefficientShearResidueInteriorDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedEquationDescent

/-!
# Whole line restrictions of every strict positive retained cocone map

At strict depth all retained charts have the same cyclic line formula, including
both original signed tangent scales.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth)
  (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
open WeierstrassModificationX WeierstrassSuccessiveX WeierstrassDilatation
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
variable (C : PushoutCocone (PolygonPinching.toComponents
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5) (by omega))
  (PolygonPinching.toNodes
    (AdjoinRoot (nodeTangentPolynomial (W.map (residue R)))) (2 * s + 5)))
local notation "F" => PolygonCyclicPushout.inputComponent Q (2 * s + 5) C.inl
local notation "w" => fun i => by
  simpa only [PolygonCyclicAtlas.next_eq_rotate] using
    PolygonCyclicPushout.input_condition Q (2 * s + 5) (by omega) C.inl C.inr C.condition i

variable (i : Fin (s + 1))
local notation "d" => data ⟨i.val + 1, by omega⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (show
  2 * (start + (i.val + 1)) ≤ depth from by omega) h3 h4
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hr" => residueTangentEquation_root W
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm
  (show 0 < start + i.val from by omega)
local notation "U" => rootShearCurve (W.map (algebraMap R Q)) r
local notation "c" => algebraMap R Q (d).b6
local notation "h2" => coefficientShear_a₂_zero W Q r hr
local notation "I" => coefficientShearRetainedEquationIso data Q r (s + 1) hs
  i hscale hp (lin).1 (lin).2
local notation "D" => coefficientShearResidueStrictPositiveAtlasCoconeMap
  hπ hm data s hs hk hstart h3 h4 h6 hc C

/-- Every full first retained line maps to its preceding cyclic component. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_first_line :
    middleLineImmersion U c h2 0 (middle_first_root U) ≫ (I).hom ≫ D (.inr i) =
      ProjectiveLine.chartScaling Q a ≫ ProjectiveLine.left Q ≫
        F ⟨i.val + 1, by omega⟩ := by
  rw [coefficientShearResidueStrictPositiveAtlasCoconeMap_retained]
  exact coefficientShearResidueStrictPositiveRetainedDesc_first_line
    hπ hm data s hs hk h3 h4 h6 hc i hstart F w

/-- Every full opposite retained line maps to its preceding opposite component. -/
theorem coefficientShearResidueStrictPositiveAtlasCoconeMap_second_line :
    middleLineImmersion U c h2 (-(U).a₁) (middle_second_root U) ≫
      (I).hom ≫ D (.inr i) =
        ProjectiveLine.chartScaling Q (-a) ≫ ProjectiveLine.right Q ≫
          F ⟨2 * s + 4 - i.val, by omega⟩ := by
  rw [coefficientShearResidueStrictPositiveAtlasCoconeMap_retained]
  exact coefficientShearResidueStrictPositiveRetainedDesc_second_line
    hπ hm data s hs hk h3 h4 h6 hc i hstart F w

end FLT.Mazur.WeierstrassDividedDepth
