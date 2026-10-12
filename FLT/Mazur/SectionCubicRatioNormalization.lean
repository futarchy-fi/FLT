/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedPowerGenerators
public import FLT.Mazur.SectionGeneratorScalar

/-!
# Normalizing cubic products of degree-three sections

A generator of the degree-three line has a generating cube in degree nine.
Dividing a cubic product by this cube multiplies the three original ratios.
This supplies scalar equations on every generator chart over arbitrary bases.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.FCurve
open ModuleLineBundleTensorPullback SectionGradedMultiplication
open SectionGradedSum SectionGradedPowerGenerators
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {X : Scheme} (L : X.Modules)

/-- The actual cubic product of three sections in the degree-three line. -/
def degreeThreeCubicProduct (U : X.Opens) (a b c : Γ(tensorPower L 3, U)) :
    Γ(tensorPower L 9, U) := mul L U 6 3 (mul L U 3 3 a b) c

/-- The cube of one section is the section representing its graded ring cube. -/
theorem degreeThreeCubicProduct_self (s : Γ(tensorPower L 3, ⊤)) :
    degreeThreeCubicProduct L ⊤ s s s = powerSection L 3 s 3 := by
  apply DirectSum.of_injective (β := Piece L ⊤) 9
  change of L ⊤ 9 (degreeThreeCubicProduct L ⊤ s s s) =
    of L ⊤ 9 (powerSection L 3 s 3)
  rw [degreeThreeCubicProduct, ← mul_of L ⊤ 6 3, ← mul_of L ⊤ 3 3,
    of_powerSection L 3 s 3]
  simp only [pow_succ, pow_zero, one_mul]

/-- The cubic denominator detects scalars on every original generator subopen. -/
theorem degreeThreeCubicProduct_smul_injective (hL : LocallyFreeRankOne L)
    (s : Γ(tensorPower L 3, ⊤)) (U : X.Opens)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L 3) s) :
    Function.Injective (fun r : Γ(X, U) ↦ r •
      (tensorPower L 9).presheaf.map U.leTop.op (degreeThreeCubicProduct L ⊤ s s s)) := by
  rw [degreeThreeCubicProduct_self]
  exact smul_powerSection_injective L hL 3 s 3 U hU

/-- Multiplying the three ratios recovers the restricted cubic product. -/
theorem degreeThreeCubicProduct_ratios (s a b c : Γ(tensorPower L 3, ⊤))
    (U : X.Opens) (hU : U ≤ sectionGeneratorOpen (tensorPower L 3) s) :
    (sectionRatioOn (tensorPower L 3) s U hU a *
      sectionRatioOn (tensorPower L 3) s U hU b *
      sectionRatioOn (tensorPower L 3) s U hU c) •
        (tensorPower L 9).presheaf.map U.leTop.op (degreeThreeCubicProduct L ⊤ s s s) =
      (tensorPower L 9).presheaf.map U.leTop.op (degreeThreeCubicProduct L ⊤ a b c) := by
  simp only [degreeThreeCubicProduct]
  simp only [mul_restrict L U.leTop 6 3, mul_restrict L U.leTop 3 3]
  rw [← smul_mul_smul, ← smul_mul_smul]
  erw [sectionRatioOn_smul (tensorPower L 3) s U hU a,
    sectionRatioOn_smul (tensorPower L 3) s U hU b,
    sectionRatioOn_smul (tensorPower L 3) s U hU c]
  rfl

end FLT.Mazur.FCurve
