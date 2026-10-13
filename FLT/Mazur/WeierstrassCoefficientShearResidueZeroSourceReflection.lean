/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualityReflection
public import FLT.Mazur.WeierstrassCoefficientShearResidueSourceInvolution
import all FLT.Mazur.WeierstrassCoefficientShearResidueZeroEqualityReflection

/-!
# Full start-zero normalization reflection

The original coproduct intertwines residue conjugation. Every full parameter
changes coefficients before reciprocity, with the inverse original terminal unit.
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
  (s : ℕ) (hs : s + 1 ≤ n) (he : 2 * (0 + (s + 1)) = depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6next : W.a₆ ∉ maximalIdeal R ^ (depth + 1)) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "hk" => Nat.le_of_eq he
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "d" => data ⟨1, by omega⟩
local notation "hres" => nodalDepth_residue_uniformizer hm
local notation "F" => coefficientShearResidueExteriorLift hπ data (s + 1) hs d
  (by dsimp; omega) hres a
local notation "B" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hk h3 h4 hc
local notation "T" => coefficientShearResidueEqualityComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "ρ" => ProjectiveLine.endpointReversal Q

local notation "C" => coefficientShearResidueZeroEqualityCycleComponent
  hπ hm data s hs he h3 h4 h6next hc
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "cunit" => nodalDepth_tangent_constant_isUnit hm e he h6next

/-- The start-zero terminal scale retains the original nonzero constant. -/
def coefficientShearResidueZeroReflectionScale (i : Fin (2 * s + 2)) : Qˣ :=
  if i.val = s + 1 then (cunit).unit⁻¹ else 1
local notation "c" => coefficientShearResidueZeroReflectionScale hm data s hs he h6next
local notation "p" => PolygonPinching.semilinearScaledParameter (f).toRingHom c

omit [IsDomain R] [IsBezout R] in
/-- All other full parameters use the unscaled reciprocal after coefficient conjugation. -/
theorem coefficientShearResidueZeroReflectionScale_other (i : Fin (2 * s + 2))
    (hi : i.val ≠ s + 1) : p i = P ≫ ρ := by
  simp only [PolygonPinching.semilinearScaledParameter,
    coefficientShearResidueZeroReflectionScale, ite_eq_right hi,
    ProjectiveLine.scaledEndpointReversal, ProjectiveLine.scaling_one, Category.comp_id]

/-- Uniform reflection retains every complete start-zero equality component. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityCycleComponent_reflection
    (i : Fin (2 * s + 2)) : C i ≫ σ = p i ≫ C (PolygonPinching.reflectIndex i) := by
  have ht : PolygonPinching.reflectIndex (⟨s + 1, by omega⟩ : Fin (2 * s + 2)) =
      ⟨s + 1, by omega⟩ := by
    apply Fin.ext
    rw [PolygonPinching.reflectIndex_val _ (by
      intro h; have := congrArg Fin.val h; simp at this)]
    dsimp only
    omega
  by_cases hz : i.val = 0
  · have hi : i = 0 := Fin.ext hz
    subst i
    rw [coefficientShearResidueZeroReflectionScale_other _ _ _ _ _ _ _ (by simp),
      PolygonPinching.reflectIndex_zero, Category.assoc]
    exact coefficientShearResidueZeroEqualityCycleComponent_exterior_conjugation ..
  have hv : (PolygonPinching.reflectIndex i).val = 2 * s + 2 - i.val :=
    PolygonPinching.reflectIndex_val i (by intro h; exact hz (congrArg Fin.val h))
  by_cases hb : i.val ≤ s
  · let j : Fin s := ⟨i.val - 1, by omega⟩
    have hi : i = ⟨j.val + 1, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    have hr : PolygonPinching.reflectIndex i = ⟨2 * s + 1 - j.val, by omega⟩ :=
      Fin.ext (by dsimp [j]; omega)
    rw [hr, coefficientShearResidueZeroReflectionScale_other _ _ _ _ _ _ _ (by omega),
      Category.assoc]
    conv_lhs => rw [hi]
    exact coefficientShearResidueZeroEqualityCycleComponent_first_conjugation ..
  by_cases heq : i.val = s + 1
  · have hi : i = ⟨s + 1, by omega⟩ := Fin.ext heq
    rw [hi, ht]
    change C ⟨s + 1, by omega⟩ ≫ σ =
      (P ≫ ProjectiveLine.scaledEndpointReversal Q (c ⟨s + 1, by omega⟩)) ≫ _
    simp only [coefficientShearResidueZeroReflectionScale, ↓reduceIte, Category.assoc]
    exact coefficientShearResidueZeroEqualityCycleComponent_terminal_conjugation ..
  · let j : Fin s := ⟨2 * s + 1 - i.val, by omega⟩
    have hi : i = ⟨2 * s + 1 - j.val, by omega⟩ := Fin.ext (by dsimp [j]; omega)
    have hr : PolygonPinching.reflectIndex i = ⟨j.val + 1, by omega⟩ :=
      Fin.ext (by dsimp [j]; omega)
    rw [hr, coefficientShearResidueZeroReflectionScale_other _ _ _ _ _ _ _ heq,
      Category.assoc]
    conv_lhs => rw [hi]
    exact coefficientShearResidueZeroEqualityCycleComponent_second_conjugation ..

local notation "N" => coefficientShearResidueZeroEqualityCycleCoproduct
  hπ hm data s hs he h3 h4 h6next hc

/-- The entire original start-zero normalization coproduct intertwines conjugation. -/
@[reassoc] theorem coefficientShearResidueZeroEqualityCycleCoproduct_conjugation :
    (N).left ≫ σ = PolygonPinching.semilinearScaledComponents (f).toRingHom c ≫ (N).left := by
  apply OverCoproductScheme.hom_ext (fun _ : Fin (2 * s + 2) => PolygonPinching.component Q)
  intro i
  change (PolygonPinching.componentι Q (2 * s + 2) i).left ≫ _ =
    (PolygonPinching.componentι Q (2 * s + 2) i).left ≫ _
  rw [coefficientShearResidueZeroEqualityCycleCoproduct_ι_assoc,
    PolygonPinching.componentι_semilinearScaledComponents_assoc,
    coefficientShearResidueZeroEqualityCycleCoproduct_ι]
  exact coefficientShearResidueZeroEqualityCycleComponent_reflection ..

omit [IsDomain R] [IsBezout R] in
/-- Every start-zero scale is fixed by the actual residue coefficient conjugation. -/
theorem coefficientShearResidueZeroReflectionScale_conjugation (i : Fin (2 * s + 2)) :
    Units.map (f).toRingHom (c i) = c i := by
  unfold coefficientShearResidueZeroReflectionScale
  split_ifs
  · rw [map_inv, coefficientShearResidueTerminalUnit_conjugation hm data s hs he h6next]
  · exact map_one _

omit [IsDomain R] [IsBezout R] in
/-- Reflection preserves the start-zero terminal position and its original scale. -/
theorem coefficientShearResidueZeroReflectionScale_reflect (i : Fin (2 * s + 2)) :
    c (PolygonPinching.reflectIndex i) = c i := by
  have hi : (PolygonPinching.reflectIndex i).val = s + 1 ↔ i.val = s + 1 := by
    by_cases hz : i = 0
    · subst i
      simp only [PolygonPinching.reflectIndex_zero, Fin.val_zero]
    · rw [PolygonPinching.reflectIndex_val i hz]
      have := i.isLt
      omega
  simp only [coefficientShearResidueZeroReflectionScale, hi]

omit [IsDomain R] [IsBezout R] in
/-- The entire start-zero normalization reflection is an involution. -/
@[reassoc] theorem coefficientShearResidueZeroSourceReflection_involutive :
    PolygonPinching.semilinearScaledComponents (f).toRingHom c ≫
      PolygonPinching.semilinearScaledComponents (f).toRingHom c = 𝟙 _ :=
  PolygonPinching.semilinearScaledComponents_involutive (f).toRingHom
    (tangentResidueConjugation_comp_self (W := W)) c
    (coefficientShearResidueZeroReflectionScale_conjugation hm data s hs he h6next)
    (coefficientShearResidueZeroReflectionScale_reflect hm data s hs he h6next)

end FLT.Mazur.WeierstrassDividedDepth
