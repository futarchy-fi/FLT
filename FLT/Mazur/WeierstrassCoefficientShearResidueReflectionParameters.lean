/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueCycleReflection
public import FLT.Mazur.CyclicPinchingSemilinearScaledSources
public import FLT.Mazur.CyclicPinchingReflectionIndices
public import FLT.Mazur.ProjectiveLineCoefficientEndpoints
public import FLT.Mazur.ProjectiveLineScaledReversalConjugation
public import FLT.Mazur.NodeTangentGluedCoefficients

/-!
# Uniform scaled semilinear reflection on all original residue components

The terminal uses the inverse of the actual nonzero equation constant in the
reversed cyclic coordinate. Every other complete component uses unit scale.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
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
local notation "hk" => Nat.le_of_eq he
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueBranchComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueCycleComponent
  hπ hm data s hs he hstart h3 h4 h6 h6next hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm e he h6next

/-- The original scale at every cyclic position, including the nonzero terminal constant. -/
def coefficientShearResidueReflectionScale (i : Fin (2 * s + 4)) : Qˣ :=
  if i.val = s + 2 then (cunit).unit⁻¹ else 1
local notation "c" => coefficientShearResidueReflectionScale hm data s hs he h6next

/-- The complete original component parameter, with coefficient change before reciprocity. -/
def coefficientShearResidueReflectionParameter (i : Fin (2 * s + 4)) :=
  PolygonPinching.semilinearScaledParameter (f).toRingHom c i
local notation "p" => coefficientShearResidueReflectionParameter hm data s hs he h6next

omit [IsDomain R] [IsBezout R] in
/-- The terminal parameter retains the inverse original constant after coefficient conjugation. -/
theorem coefficientShearResidueReflectionParameter_terminal :
    p ⟨s + 2, by omega⟩ =
      P ≫ ProjectiveLine.scaledEndpointReversal Q (cunit).unit⁻¹ := by
  simp only [coefficientShearResidueReflectionParameter, coefficientShearResidueReflectionScale,
    PolygonPinching.semilinearScaledParameter, ↓reduceIte]

omit [IsDomain R] [IsBezout R] in
/-- Every other full parameter is coefficient conjugation followed by endpoint reversal. -/
theorem coefficientShearResidueReflectionParameter_other (i : Fin (2 * s + 4))
    (hi : i.val ≠ s + 2) : p i = P ≫ ρ := by
  simp only [coefficientShearResidueReflectionParameter, coefficientShearResidueReflectionScale,
    PolygonPinching.semilinearScaledParameter, ite_eq_right hi,
    ProjectiveLine.scaledEndpointReversal, ProjectiveLine.scaling_one, Category.comp_id]

/-- Uniform reflection retains all full original components and their coefficient action. -/
@[reassoc] theorem coefficientShearResidueCycleComponent_reflection (i : Fin (2 * s + 4)) :
    C i ≫ σ = p i ≫ C (PolygonPinching.reflectIndex i) := by
  by_cases hz : i.val = 0
  · have hi : i = 0 := Fin.ext hz
    subst i
    rw [coefficientShearResidueReflectionParameter_other _ _ _ _ _ _ _ (by simp),
      PolygonPinching.reflectIndex_zero, Category.assoc]
    exact coefficientShearResidueCycleComponent_exterior_conjugation
      hπ hm data s hs he hstart h3 h4 h6 h6next hc
  by_cases hb : i.val ≤ s + 1
  · let j : Fin (s + 1) := ⟨i.val - 1, by omega⟩
    have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hi, PolygonPinching.reflectIndex_firstChain,
      coefficientShearResidueReflectionParameter_other _ _ _ _ _ _ _ (by dsimp; omega),
      Category.assoc]
    exact coefficientShearResidueCycleComponent_first_conjugation
      hπ hm data s hs he hstart h3 h4 h6 h6next hc j
  by_cases ht : i.val = s + 2
  · have hi : i = ⟨s + 2, by omega⟩ := Fin.ext ht
    rw [hi, PolygonPinching.reflectIndex_terminal,
      coefficientShearResidueReflectionParameter_terminal, Category.assoc]
    exact coefficientShearResidueCycleComponent_terminal_conjugation
      hπ hm data s hs he hstart h3 h4 h6 h6next hc
  · let j : Fin (s + 1) := ⟨2 * s + 3 - i.val, by omega⟩
    have hi : i = ⟨2 * s + 3 - j.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    rw [hi, PolygonPinching.reflectIndex_secondChain,
      coefficientShearResidueReflectionParameter_other _ _ _ _ _ _ _ (by dsimp [j]; omega),
      Category.assoc]
    exact coefficientShearResidueCycleComponent_second_conjugation
      hπ hm data s hs he hstart h3 h4 h6 h6next hc j

end FLT.Mazur.WeierstrassDividedDepth
