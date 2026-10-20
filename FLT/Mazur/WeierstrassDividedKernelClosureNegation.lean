/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.DenseClosedRestriction
public import FLT.Mazur.WeierstrassDividedKernelClosure
public import FLT.Mazur.WeierstrassDividedGenericNegation

/-!
# The full divided kernel closure is stable under the constructed inverse

The original generic inverse determines an actual automorphism of the entire
schematic closure in each finite projective model. The restriction retains
the original generic source, integral inclusion and coefficient morphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [Field K] [Algebra R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]
  (neg : H ⟶ H) (hn : neg ≫ i = i ≫ integralCurveNegation (W.map (algebraMap R K)))
local notation "D" => finiteGlobalKernelToClosure hπ data j hj hΔ i
local notation "I" => finiteGlobalKernelClosureInclusion hπ data j hj hΔ i
local notation "N" => finiteGlobalNegation hπ data j hj
local notation "C" => finiteGlobalKernelClosure hπ data j hj hΔ i

include hn in
omit [IsClosedImmersion i] in
/-- The original generic inverse supplies the exact square on the dense source. -/
theorem finiteKernelToClosure_negation_square :
    D ≫ (I ≫ N) = (neg ≫ D) ≫ I := by
  simp only [Category.assoc, finiteGlobalKernelToClosure_inclusion,
    finiteGlobalKernelToClosure_inclusion_assoc]
  rw [finiteGlobalGenericCurve_negation, ← Category.assoc, ← hn, Category.assoc]

/-- Restrict the constructed finite-model inverse to the full original kernel closure. -/
def finiteKernelClosureNegation : C ⟶ C :=
  DenseClosedRestriction.lift D I (I ≫ N) (neg ≫ D)
    (finiteKernelToClosure_negation_square hπ data j hj hΔ i neg hn)

/-- The restricted negative is precisely the actual entire-model inverse. -/
@[reassoc] theorem finiteKernelClosureNegation_inclusion :
    finiteKernelClosureNegation hπ data j hj hΔ i neg hn ≫ I = I ≫ N :=
  DenseClosedRestriction.lift_inclusion _ _ _ _ _

/-- The full original generic inverse survives restriction to the closure. -/
@[reassoc] theorem finiteKernelToClosure_negation :
    D ≫ finiteKernelClosureNegation hπ data j hj hΔ i neg hn = neg ≫ D :=
  DenseClosedRestriction.dense_lift _ _ _ _ _

/-- The constructed inverse fixes the original integral coefficient morphism. -/
@[reassoc] theorem finiteKernelClosureNegation_structure :
    finiteKernelClosureNegation hπ data j hj hΔ i neg hn ≫
        finiteGlobalKernelClosureStructure hπ data j hj hΔ i =
      finiteGlobalKernelClosureStructure hπ data j hj hΔ i := by
  rw [finiteGlobalKernelClosureStructure, finiteKernelClosureNegation_inclusion_assoc,
    finiteGlobalNegation_structure]

/-- The inverse is involutive on the entire schematic closure, including every special point. -/
@[reassoc] theorem finiteKernelClosureNegation_comp :
    finiteKernelClosureNegation hπ data j hj hΔ i neg hn ≫
      finiteKernelClosureNegation hπ data j hj hΔ i neg hn = 𝟙 C := by
  apply (cancel_mono I).mp
  simp only [Category.assoc, finiteKernelClosureNegation_inclusion,
    finiteKernelClosureNegation_inclusion_assoc, finiteGlobalNegation_comp,
    Category.comp_id, Category.id_comp]

/-- An actual automorphism of the full closure extends its original generic inverse. -/
def finiteKernelClosureNegationIso : C ≅ C where
  hom := finiteKernelClosureNegation hπ data j hj hΔ i neg hn
  inv := finiteKernelClosureNegation hπ data j hj hΔ i neg hn
  hom_inv_id := finiteKernelClosureNegation_comp hπ data j hj hΔ i neg hn
  inv_hom_id := finiteKernelClosureNegation_comp hπ data j hj hΔ i neg hn

end FLT.Mazur.WeierstrassDividedDepth
