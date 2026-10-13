/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassResidueTangentComponentData
public import FLT.Mazur.WeierstrassCoefficientShearTerminalSemilinear

/-!
# The actual residue-tangent terminal pair before equality depth

The original strict depth bound supplies zero constant. Both scale cases yield
independent complete terminal components at the final stage, with the actual
full coefficient exchange and integral tangent specialization.
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
  (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + (s + 1)) < depth)
  (h3 : W.a₃ ∈ maximalIdeal R ^ (depth + 1))
  (h4 : W.a₄ ∈ maximalIdeal R ^ (depth + 1))
  (h6 : W.a₆ ∈ maximalIdeal R ^ depth) (hc : IsUnit W.c₄)
local notation "V" => W.map (residue R)
local notation "Q" => AdjoinRoot (nodeTangentPolynomial V)
local notation "r" => AdjoinRoot.root (nodeTangentPolynomial V)
variable [Fact (Irreducible (nodeTangentPolynomial (W.map (residue R))))]
local notation "e" => data ⟨s + 1, Nat.lt_succ_of_le hs⟩
local notation "lin" => nodalDepth_tangent_linear_zero hπ hm e (by dsimp; omega) h3 h4
local notation "g6" => nodalDepth_tangent_constant_zero hπ hm e hk h6
local notation "a" => residueTangentComponentUnit W h3 h4 hc
local notation "ha" => residueTangentComponentUnit_val W h3 h4 hc
local notation "hr" => residueTangentEquation_root W
local notation "hp" => residueTangentEquation_zero W π
  (hm ▸ Ideal.mem_span_singleton_self π)
local notation "g" => coefficientShearGluedStructure hπ data Q r (s + 1) hs
local notation "σ" => coefficientShearResidueTangentConjugation hπ data (s + 1) hs
local notation "f" => tangentResidueConjugationAlgHom (W := W)
local notation "P" => ProjectiveLine.coefficientMap (f).toRingHom

/-- The independent terminal pair for either scale, transported to the common final stage. -/
def coefficientShearResidueTerminalComponent (i : Fin 2) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data Q r (s + 1) hs :=
  (if h : 0 < start + s then
    if i = 0 then
      coefficientShearRootTerminalFirstComponent hπ data Q r s hs
        (nodalDepth_tangent_scale_zero (W := W) hm h) hp (lin).1 (lin).2 g6 hr a ha
    else
      coefficientShearRootTerminalSecondComponent hπ data Q r s hs
        (nodalDepth_tangent_scale_zero (W := W) hm h) hp (lin).1 (lin).2 g6 hr a ha
  else
    let hscale : algebraMap R Q (π ^ (start + s)) = 1 := by
      rw [show start + s = 0 by omega, pow_zero, map_one]
    if i = 0 then
      coefficientShearRootTerminalZeroFirstComponent hπ data Q r s hs
        hscale hp (lin).1 (lin).2 g6 hr a ha
    else
      coefficientShearRootTerminalZeroSecondComponent hπ data Q r s hs
        hscale hp (lin).1 (lin).2 g6 hr a ha)
local notation "C" => coefficientShearResidueTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc

/-- Both complete terminal components preserve the original residue coefficient structure. -/
@[reassoc] theorem coefficientShearResidueTerminalComponent_structure (i : Fin 2) :
    C i ≫ g = ProjectiveLine.toBase Q := by
  unfold coefficientShearResidueTerminalComponent
  split_ifs
  · exact coefficientShearRootTerminalFirstComponent_structure ..
  · exact coefficientShearRootTerminalSecondComponent_structure ..
  · exact coefficientShearRootTerminalZeroFirstComponent_structure ..
  · exact coefficientShearRootTerminalZeroSecondComponent_structure ..

/-- Actual conjugation exchanges each full terminal pair at the same final stage. -/
@[reassoc] theorem coefficientShearResidueTerminalComponent_conjugation (i : Fin 2) :
    C i ≫ σ = P ≫ C i.rev := by
  unfold coefficientShearResidueTerminalComponent
  rw [coefficientShearResidueTangentConjugation]
  by_cases h : 0 < start + s
  · simp only [dite_eq_left h]
    fin_cases i
    · simpa only [Category.assoc, Fin.rev, Fin.ext_iff, Fin.val_zero, ↓reduceIte,
        Nat.reduceSub, Nat.reduceAdd, Nat.one_ne_zero, Nat.zero_ne_one] using
        coefficientShearRootTerminalFirstComponent_semilinear
        hπ data Q r s hs
        (nodalDepth_tangent_scale_zero (W := W) hm h)
        hp (lin).1 (lin).2 g6 hr a ha
        (residueTangentCompanion W) (residueTangentCompanion_equation W) (-a)
        (residueTangentComponentUnit_companion W h3 h4 hc) (residueTangentCompanion_sum W)
        f (residueTangentCompanion_conjugation W)
    · simpa only [Category.assoc, Fin.rev, Fin.ext_iff, Fin.val_zero, ↓reduceIte,
        Nat.reduceSub, Nat.reduceAdd, Nat.one_ne_zero, Nat.zero_ne_one] using
        coefficientShearRootTerminalSecondComponent_semilinear
        hπ data Q r s hs
        (nodalDepth_tangent_scale_zero (W := W) hm h)
        hp (lin).1 (lin).2 g6 hr a ha
        (residueTangentCompanion W) (residueTangentCompanion_equation W) (-a)
        (residueTangentComponentUnit_companion W h3 h4 hc) (residueTangentCompanion_sum W)
        f (residueTangentCompanion_conjugation W)
  · simp only [dite_eq_right h]
    fin_cases i
    · simpa only [Category.assoc, Fin.rev, Fin.ext_iff, Fin.val_zero, ↓reduceIte,
        Nat.reduceSub, Nat.reduceAdd, Nat.one_ne_zero, Nat.zero_ne_one] using
        coefficientShearRootTerminalZeroFirstComponent_semilinear
        hπ data Q r s hs
        hp (lin).1 (lin).2 g6 hr a ha
        (residueTangentCompanion W) (residueTangentCompanion_equation W) (-a)
        (residueTangentComponentUnit_companion W h3 h4 hc) (residueTangentCompanion_sum W)
        f (residueTangentCompanion_conjugation W)
        (by rw [show start + s = 0 by omega, pow_zero, map_one])
    · simpa only [Category.assoc, Fin.rev, Fin.ext_iff, Fin.val_zero, ↓reduceIte,
        Nat.reduceSub, Nat.reduceAdd, Nat.one_ne_zero, Nat.zero_ne_one] using
        coefficientShearRootTerminalZeroSecondComponent_semilinear
        hπ data Q r s hs
        hp (lin).1 (lin).2 g6 hr a ha
        (residueTangentCompanion W) (residueTangentCompanion_equation W) (-a)
        (residueTangentComponentUnit_companion W h3 h4 hc) (residueTangentCompanion_sum W)
        f (residueTangentCompanion_conjugation W)
        (by rw [show start + s = 0 by omega, pow_zero, map_one])

local notation "A" => AdjoinRoot (nodeTangentPolynomial W)
local notation "rA" => AdjoinRoot.root (nodeTangentPolynomial W)
local notation "M" => coefficientShearTangentSpecialization hπ data (s + 1) hs

/-- The entire terminal pair in the original integral tangent target. -/
def coefficientShearIntegralTerminalComponent (i : Fin 2) :
    ProjectiveLine.scheme Q ⟶ coefficientShearGlued hπ data A rA (s + 1) hs := C i ≫ M
local notation "I" => coefficientShearIntegralTerminalComponent
  hπ hm data s hs hk h3 h4 h6 hc

/-- Actual integral conjugation retains the full semilinear exchange of each terminal pair. -/
@[reassoc] theorem coefficientShearIntegralTerminalComponent_conjugation (i : Fin 2) :
    I i ≫ coefficientShearTangentConjugation hπ data (s + 1) hs = P ≫ I i.rev := by
  simp only [coefficientShearIntegralTerminalComponent, Category.assoc]
  rw [← coefficientShearTangentSpecialization_conjugation, ← Category.assoc,
    coefficientShearResidueTerminalComponent_conjugation]
  simp only [Category.assoc]

end FLT.Mazur.WeierstrassDividedDepth
