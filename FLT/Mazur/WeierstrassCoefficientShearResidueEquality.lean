/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResidueTangentComponentData
public import FLT.Mazur.WeierstrassCoefficientShearEqualitySemilinear

/-!
# The actual residue-tangent equality component

Both incidence scale cases give a complete component at the same final stage.
All root, tangent-unit and coefficient hypotheses come from the original nodal
depth conditions. Actual residue conjugation retains the constant-scaled reversal.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0)
  (hm : maximalIdeal R = Ideal.span {π}) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (start + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "d" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm d (Nat.le_of_eq he) h3 h4
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm d he h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)

/-- Independently completed equality component over the actual residue tangent field. -/
def coefficientShearResidueEqualityComponent :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  if h : 0 < start + s then
    coefficientShearRootEqualityComponent hπ data Q r s hs
      (nodalDepth_tangent_scale_zero (W := W) hm h) hp (lin).1 (lin).2 cunit hr a ha
  else
    coefficientShearScaleOneEqualityComponent hπ data Q r s hs
      (by rw [show start + s = 0 by omega, pow_zero, map_one])
      hp (lin).1 (lin).2 cunit hr a ha
local notation "C" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6 hc

/-- The entire actual equality component has the original residue coefficient structure. -/
@[reassoc] theorem coefficientShearResidueEqualityComponent_structure :
    C ≫ g = ProjectiveLine.toBase Q := by
  unfold coefficientShearResidueEqualityComponent
  split_ifs
  · exact coefficientShearRootEqualityComponent_structure ..
  · exact coefficientShearScaleOneEqualityComponent_structure ..

/-- Actual residue conjugation acts on the full component by coefficient change and c/T. -/
@[reassoc] theorem coefficientShearResidueEqualityComponent_conjugation :
    C ≫ σ = ProjectiveLine.coefficientMap (f).toRingHom ≫
      ProjectiveLine.scaledEndpointReversal Q (cunit).unit ≫ C := by
  unfold coefficientShearResidueEqualityComponent
  split_ifs with h
  · exact coefficientShearRootEqualityComponent_semilinear
      hπ data Q r s hs (nodalDepth_tangent_scale_zero (W := W) hm h)
      hp (lin).1 (lin).2 cunit hr a ha
      (residueTangentCompanion W) (residueTangentCompanion_equation W) (-a)
      (residueTangentComponentUnit_companion W h3 h4 hc) (residueTangentCompanion_sum W)
      f (residueTangentCompanion_conjugation W)
  · exact coefficientShearScaleOneEqualityComponent_semilinear
      hπ data Q r s hs hp (lin).1 (lin).2 cunit hr a ha
      (residueTangentCompanion W) (residueTangentCompanion_equation W) (-a)
      (residueTangentComponentUnit_companion W h3 h4 hc) (residueTangentCompanion_sum W)
      f (residueTangentCompanion_conjugation W)
      (by rw [show start + s = 0 by omega, pow_zero, map_one])

local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "M" => coefficientShearTangentSpecialization hπ data (s + 1) hs

/-- Specialize the entire independently completed component into the integral tangent model. -/
def coefficientShearIntegralEqualityComponent :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data A rA (s + 1) hs := C ≫ M
local notation "I" => coefficientShearIntegralEqualityComponent
  hπ hm data s hs he h3 h4 h6 hc

/-- The actual integral-target component retains the same full scaled semilinear reflection. -/
@[reassoc] theorem coefficientShearIntegralEqualityComponent_conjugation :
    I ≫ coefficientShearTangentConjugation hπ data (s + 1) hs =
      ProjectiveLine.coefficientMap (f).toRingHom ≫
        ProjectiveLine.scaledEndpointReversal Q (cunit).unit ≫ I := by
  rw [coefficientShearIntegralEqualityComponent, Category.assoc,
    ← coefficientShearTangentSpecialization_conjugation, ← Category.assoc,
    coefficientShearResidueEqualityComponent_conjugation]
  simp only [Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
