/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResidueTangentComponentData
public import FLT.Mazur.WeierstrassCoefficientShearInitialSemilinear
public import FLT.Mazur.WeierstrassCoefficientShearStageIso

/-!
# The actual residue-tangent initial pair at a common final stage

Construct the complete initial pair from the original nodal depth conditions.
The full residue and integral-target components exchange under the original
quadratic coefficient action, with their independent projective parameters.
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
  (hstart : 0 < start)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "h1" => show 1 ≤ n from by omega
local notation "hs'" => show 1 + s ≤ n from by omega
local notation "d" => data ⟨0, Nat.zero_lt_succ n⟩
local notation "e" => data ⟨1, Nat.lt_succ_of_le h1⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "ini" => nodalDepth_tangent_linear_zero hπ hm d (by dsimp; omega) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm d (by dsimp; omega) h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "hscale" => nodalDepth_tangent_scale_zero (W := W) hm hstart
local notation "C₁" => coefficientShearRootInitialFirstComponent hπ data Q r h1 s hs'
  hscale hp (lin).1 (lin).2 hr (ini).1 (ini).2 g6 a ha
local notation "C₂" => coefficientShearRootInitialSecondComponent hπ data Q r h1 s hs'
  hscale hp (lin).1 (lin).2 hr (ini).1 (ini).2 g6 a ha
local notation "E" => coefficientShearStageIso hπ data Q r (1 + s) (s + 1) hs' hs (by omega)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

/-- Both independent initial components, with the common final target and original branch index. -/
def coefficientShearResidueInitialComponent (i : Fin 2) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  (if i = 0 then C₁ else C₂) ≫ (E).hom
local notation "C" => coefficientShearResidueInitialComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- Both complete components preserve the original residue coefficient structure. -/
@[reassoc] theorem coefficientShearResidueInitialComponent_structure (i : Fin 2) :
    C i ≫ g = ProjectiveLine.toBase Q := by
  unfold coefficientShearResidueInitialComponent
  rw [Category.assoc, coefficientShearStageIso_structure]
  split_ifs
  · exact coefficientShearRootInitialFirstComponent_structure ..
  · exact coefficientShearRootInitialSecondComponent_structure ..

/-- Actual conjugation exchanges the full initial pair, retaining the projective parameter. -/
@[reassoc] theorem coefficientShearResidueInitialComponent_conjugation (i : Fin 2) :
    C i ≫ σ = P ≫ C i.rev := by
  unfold coefficientShearResidueInitialComponent
  rw [Category.assoc, coefficientShearResidueTangentConjugation,
    coefficientShearStageIso_specialization, ← Category.assoc]
  fin_cases i
  · simpa only [Category.assoc, Fin.rev, Fin.ext_iff, Fin.val_zero, ↓reduceIte,
      Nat.reduceSub, Nat.reduceAdd, Nat.one_ne_zero, Nat.zero_ne_one]
      using coefficientShearRootInitialFirstComponent_semilinear_assoc
      hπ data Q r h1 s hs' hscale hp (lin).1 (lin).2 hr (ini).1 (ini).2 g6 a ha
      (residueTangentCompanion W) (-a) (residueTangentComponentUnit_companion W h3 h4 hc)
      (residueTangentCompanion_equation W) (residueTangentCompanion_sum W)
      f (residueTangentCompanion_conjugation W) (E).hom
  · simpa only [Category.assoc, Fin.rev, Fin.ext_iff, Fin.val_zero, ↓reduceIte,
      Nat.reduceSub, Nat.reduceAdd, Nat.one_ne_zero, Nat.zero_ne_one]
      using coefficientShearRootInitialSecondComponent_semilinear_assoc
      hπ data Q r h1 s hs' hscale hp (lin).1 (lin).2 hr (ini).1 (ini).2 g6 a ha
      (residueTangentCompanion W) (-a) (residueTangentComponentUnit_companion W h3 h4 hc)
      (residueTangentCompanion_equation W) (residueTangentCompanion_sum W)
      f (residueTangentCompanion_conjugation W) (E).hom

local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "M" => coefficientShearTangentSpecialization hπ data (s + 1) hs

/-- The complete initial pair in the actual integral tangent target. -/
def coefficientShearIntegralInitialComponent (i : Fin 2) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data A rA (s + 1) hs := C i ≫ M
local notation "I" => coefficientShearIntegralInitialComponent
  hπ hm data s hs hk hstart h3 h4 h6 hc

/-- Specializing the initial pair intertwines actual integral tangent conjugation. -/
@[reassoc] theorem coefficientShearIntegralInitialComponent_conjugation (i : Fin 2) :
    I i ≫ coefficientShearTangentConjugation hπ data (s + 1) hs = P ≫ I i.rev := by
  simp only [coefficientShearIntegralInitialComponent, Category.assoc]
  rw [← coefficientShearTangentSpecialization_conjugation, ← Category.assoc,
    coefficientShearResidueInitialComponent_conjugation]
  simp only [Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
