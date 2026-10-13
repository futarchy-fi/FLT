/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResidueTangentComponentData
public import FLT.Mazur.WeierstrassCoefficientShearAdjacentSemilinear
public import FLT.Mazur.WeierstrassCoefficientShearScaleOneSemilinear
public import FLT.Mazur.WeierstrassCoefficientShearStageIso

/-!
# Actual residue-tangent adjacent pairs at the common final stage

Both scale cases use independent complete components. Original nodal depth
conditions supply all coefficients, and the full semilinear exchange survives
reindexing and specialization into the integral tangent model.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) ≤ depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (hc : IsUnit W.c₄) (j : Fin s)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "hj" => show j.val + 1 ≤ n from by omega
local notation "hjNext" => show j.val + 2 ≤ n from by omega
local notation "m" => s - (j.val + 1)
local notation "hs'" => show j.val + 2 + m ≤ n from by omega
local notation "e" => data ⟨j.val + 2, Nat.lt_succ_of_le hjNext⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "E" => coefficientShearStageIso hπ data Q r
  (j.val + 2 + m) (s + 1) hs' hs (by omega)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

/-- The independent retained pair for either scale, transported to the common final stage. -/
def coefficientShearResidueAdjacentComponent (i : Fin 2) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  (if h : 0 < start + j.val then
    if i = 0 then
      coefficientShearAdjacentFirstComponent hπ data Q r j.val hj hjNext m hs'
        (nodalDepth_tangent_scale_zero (W := W) hm h) hp (lin).1 (lin).2 hr a ha
    else
      coefficientShearAdjacentSecondComponent hπ data Q r j.val hj hjNext m hs'
        (nodalDepth_tangent_scale_zero (W := W) hm h) hp (lin).1 (lin).2 hr a ha
  else
    let hscale : algebraMap R Q (π ^ (start + j.val)) = 1 := by
      rw [show start + j.val = 0 by omega, pow_zero, map_one]
    if i = 0 then
      coefficientShearScaleOneFirstComponent hπ data Q r j.val hj hjNext m hs'
        hscale hp (lin).1 (lin).2 hr a ha
    else
      coefficientShearScaleOneSecondComponent hπ data Q r j.val hj hjNext m hs'
        hscale hp (lin).1 (lin).2 hr a ha) ≫ (E).hom
local notation "C" => coefficientShearResidueAdjacentComponent
  hπ hm data s hs hk h3 h4 hc j

/-- Both complete adjacent components preserve the original residue coefficient structure. -/
@[reassoc] theorem coefficientShearResidueAdjacentComponent_structure (i : Fin 2) :
    C i ≫ g = ProjectiveLine.toBase Q := by
  unfold coefficientShearResidueAdjacentComponent
  rw [Category.assoc, coefficientShearStageIso_structure]
  split_ifs
  · exact coefficientShearAdjacentFirstComponent_structure ..
  · exact coefficientShearAdjacentSecondComponent_structure ..
  · exact coefficientShearScaleOneFirstComponent_structure ..
  · exact coefficientShearScaleOneSecondComponent_structure ..

/-- Actual conjugation exchanges each full retained pair at the same final stage. -/
@[reassoc] theorem coefficientShearResidueAdjacentComponent_conjugation (i : Fin 2) :
    C i ≫ σ = P ≫ C i.rev := by
  unfold coefficientShearResidueAdjacentComponent
  rw [Category.assoc, coefficientShearResidueTangentConjugation,
    coefficientShearStageIso_specialization, ← Category.assoc]
  by_cases h : 0 < start + j.val
  · simp only [dite_eq_left h]
    fin_cases i
    · simpa only [Category.assoc, Fin.rev, Fin.ext_iff, Fin.val_zero, ↓reduceIte,
        Nat.reduceSub, Nat.reduceAdd, Nat.one_ne_zero, Nat.zero_ne_one] using
        coefficientShearAdjacentFirstComponent_semilinear_assoc
        hπ data Q r j.val hj hjNext m hs'
        (nodalDepth_tangent_scale_zero (W := W) hm h)
        hp (lin).1 (lin).2 hr a ha
        (residueTangentCompanion W) (-a) (residueTangentComponentUnit_companion W h3 h4 hc)
        (residueTangentCompanion_equation W) (residueTangentCompanion_sum W)
        f (residueTangentCompanion_conjugation W) (E).hom
    · simpa only [Category.assoc, Fin.rev, Fin.ext_iff, Fin.val_zero, ↓reduceIte,
        Nat.reduceSub, Nat.reduceAdd, Nat.one_ne_zero, Nat.zero_ne_one] using
        coefficientShearAdjacentSecondComponent_semilinear_assoc
        hπ data Q r j.val hj hjNext m hs'
        (nodalDepth_tangent_scale_zero (W := W) hm h)
        hp (lin).1 (lin).2 hr a ha
        (residueTangentCompanion W) (-a) (residueTangentComponentUnit_companion W h3 h4 hc)
        (residueTangentCompanion_equation W) (residueTangentCompanion_sum W)
        f (residueTangentCompanion_conjugation W) (E).hom
  · simp only [dite_eq_right h]
    fin_cases i
    · simpa only [Category.assoc, Fin.rev, Fin.ext_iff, Fin.val_zero, ↓reduceIte,
        Nat.reduceSub, Nat.reduceAdd, Nat.one_ne_zero, Nat.zero_ne_one] using
        coefficientShearScaleOneFirstComponent_semilinear_assoc
        hπ data Q r j.val hj hjNext m hs'
        (by rw [show start + j.val = 0 by omega, pow_zero, map_one])
        hp (lin).1 (lin).2 hr a ha
        (residueTangentCompanion W) (-a) (residueTangentComponentUnit_companion W h3 h4 hc)
        (residueTangentCompanion_equation W) (residueTangentCompanion_sum W)
        f (residueTangentCompanion_conjugation W) (E).hom
    · simpa only [Category.assoc, Fin.rev, Fin.ext_iff, Fin.val_zero, ↓reduceIte,
        Nat.reduceSub, Nat.reduceAdd, Nat.one_ne_zero, Nat.zero_ne_one] using
        coefficientShearScaleOneSecondComponent_semilinear_assoc
        hπ data Q r j.val hj hjNext m hs'
        (by rw [show start + j.val = 0 by omega, pow_zero, map_one])
        hp (lin).1 (lin).2 hr a ha
        (residueTangentCompanion W) (-a) (residueTangentComponentUnit_companion W h3 h4 hc)
        (residueTangentCompanion_equation W) (residueTangentCompanion_sum W)
        f (residueTangentCompanion_conjugation W) (E).hom

local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "M" => coefficientShearTangentSpecialization hπ data (s + 1) hs

/-- The entire adjacent pair in the original integral tangent target. -/
def coefficientShearIntegralAdjacentComponent (i : Fin 2) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data A rA (s + 1) hs := C i ≫ M
local notation "I" => coefficientShearIntegralAdjacentComponent
  hπ hm data s hs hk h3 h4 hc j

/-- Actual integral conjugation retains the full semilinear exchange of each retained pair. -/
@[reassoc] theorem coefficientShearIntegralAdjacentComponent_conjugation (i : Fin 2) :
    I i ≫ coefficientShearTangentConjugation hπ data (s + 1) hs = P ≫ I i.rev := by
  simp only [coefficientShearIntegralAdjacentComponent, Category.assoc]
  rw [← coefficientShearTangentSpecialization_conjugation, ← Category.assoc,
    coefficientShearResidueAdjacentComponent_conjugation]
  simp only [Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
