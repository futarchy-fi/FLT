/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityFirstGraphFlat

/-!
# Original truncated-base flatness suffices for first-node preservation

The literal adic graph charts are flat over K[t]/t^2. For the actual finite
branch graph, flatness over this smaller coefficient ring already forces
all original coordinate errors into the original node algebra. Thus the
remaining geometric comparison need only retain this actual coefficient
map; flatness over the larger Laurent coefficient ring is a consequence.
No flatness of the finite branch graph is asserted here.
-/

@[expose] public noncomputable section
open CategoryTheory
open scoped LaurentPolynomial
namespace FLT.Mazur.PolygonInfinitesimalStages
open PolygonSmoothing LaurentFirstStageParameter PolygonInfinitesimal
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] PolygonSmoothing.relationIdeal
  completeIdentityFirstActionUnit completeIdentityFirstActionField
  completeIdentityFirstActionNodeDefect completeIdentityFirstGraphAlgebra
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n] (i : Fin n)
local notation "R" => K[T;T⁻¹]
local notation "S" => Ring (R) 1
local notation "e" => parameter (R) 1
local notation "B" => ChartRing (e)
local notation "C" => firstNodeBranchSubalgebra (R)
local notation "F" => completeIdentityFirstActionBranchEquiv K n h i
local notation "D" => completeIdentityFirstActionNodeDefect K n h i
local notation "G" => completeIdentityFirstGraphAlgebra K n h i
local notation "σ" => reciprocalScale (e) (parameterUnit K)

/-- The finite branch graph's unchanged original truncated-base coefficient map. -/
def completeIdentityFirstGraphOriginalScalars : Ring K 1 →+* (G) :=
  (algebraMap (S) (G)).comp (stageCoefficientMap (LaurentPolynomial.C : K →+* (R)) 1)

/-- The smaller coefficient map retains the graph's actual square-zero parameter. -/
theorem completeIdentityFirstGraphOriginalScalars_parameter :
    completeIdentityFirstGraphOriginalScalars K n h i (parameter K 1) =
      algebraMap (S) (G) (e) := by
  change algebraMap (S) (G)
    (stageCoefficientMap (LaurentPolynomial.C : K →+* (R)) 1 (parameter K 1)) = _
  rw [stageCoefficientMap_parameter]

/-- Flatness over the original smaller base already makes every actual defect descend. -/
theorem completeIdentityFirstGraphOriginalFlat_defect
    (hf : (completeIdentityFirstGraphOriginalScalars K n h i).Flat) (z : B) :
    (D) z ∈ (C) := by
  let _ := (completeIdentityFirstGraphOriginalScalars K n h i).toAlgebra
  let _ : Module.Flat (Ring K 1) (G) := hf
  have hs (w : G) : ((parameter K 1) • w).val = (e) • w.val := by
    change algebraMap (S) ((S)[T;T⁻¹] × (S)[T;T⁻¹])
      (stageCoefficientMap (LaurentPolynomial.C : K →+* (R)) 1 (parameter K 1)) * w.val = _
    rw [stageCoefficientMap_parameter, Algebra.smul_def]
  let d : G := ⟨(D) z, completeIdentityFirstGraphAlgebra_defect K n h i z⟩
  have hd : parameter K 1 • d = 0 := by
    apply Subtype.ext
    rw [hs]
    exact completeIdentityFirstActionNodeDefect_parameter K n h i z
  obtain ⟨w, hw⟩ := (flat_parameter_smul_eq_zero_iff K 0 (G) d).mp hd
  have he : (e) • w.val = (D) z := by
    have hh := congrArg Subtype.val hw
    change (parameter K 1 ^ 1 • w).val = (D) z at hh
    simpa only [pow_one, hs] using hh
  rw [← he]
  exact completeIdentityFirstGraphAlgebra_parameter K n h i w.val w.property

/-- The unchanged original action preserves the node if its actual graph is flat over K[t]/t^2. -/
theorem completeIdentityFirstGraphOriginalFlat_preserves
    (hf : (completeIdentityFirstGraphOriginalScalars K n h i).Flat)
    (p : (S)[T;T⁻¹] × (S)[T;T⁻¹]) (hp : p ∈ (C)) : (F) p ∈ (C) := by
  obtain ⟨z, hz⟩ := hp
  change firstNodeBranchPair (R) z = p at hz
  rw [← hz]
  have hd := completeIdentityFirstGraphOriginalFlat_defect K n h i hf z
  have hs : firstNodeBranchPair (R) ((σ) z) ∈ (C) := ⟨_, rfl⟩
  simpa only [completeIdentityFirstActionNodeDefect_apply, sub_add_cancel]
    using (C).add_mem hd hs

/-- For this actual graph, original-base flatness implies Laurent-coefficient flatness. -/
theorem completeIdentityFirstGraphOriginalFlat_laurent
    (hf : (completeIdentityFirstGraphOriginalScalars K n h i).Flat) : Module.Flat (S) (G) :=
  (completeIdentityFirstGraphFlat_iff_preserves K n h i).mpr
    (completeIdentityFirstGraphOriginalFlat_preserves K n h i hf)

/-- Original-base flatness of the finite branch graph proves the unchanged first positive law. -/
theorem completeIdentityFiniteLaw_one_of_graphOriginalFlat
    (hf : (completeIdentityFirstGraphOriginalScalars K n h i).Flat) :
    universalEdgeScaling (Ring K 1) ≫ completeIdentityStageTorus K n h i 1 =
      completeIdentityFiniteOriginalMul K n h i 1 :=
  completeIdentityFiniteLaw_one_of_branch_preservation K n h i
    (completeIdentityFirstGraphOriginalFlat_preserves K n h i hf)

end FLT.Mazur.PolygonInfinitesimalStages
