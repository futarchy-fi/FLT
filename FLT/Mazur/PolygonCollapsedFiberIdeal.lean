/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCollapsedIdealDetection

/-!
# The collapsed fiber on the full cyclic nodal atlas

The original normalization formulas uniquely determine the entire fiber ideal.
Every node between two omitted components retains its full nodal chart, rather
than just the two branches or its underlying support.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonCollapsedFiberIdeal
open PolygonCyclicAtlas PolygonOneGonContraction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) (i : Fin n)
local notation "p" => normalization K n h
local notation "q" => nodes K n h
local notation "hp" => PolygonCyclicPushout.isPushout K n h (by omega)
local notation "F" => fiberIdeal K n (by omega) p q hp i

/-- The full fiber ideal vanishes on each actual omitted component morphism. -/
theorem component_omitted {j : Fin n} (hj : j ≠ i) :
    (F).comap (componentMap K n h j) = ⊥ := by
  have he := fiberIdeal_omitted K n (by omega) p q hp i hj
  rw [componentι_normalization] at he
  exact he

/-- Its restriction to the retained complete component is the actual one-gon node fiber. -/
theorem component_retained :
    (F).comap (componentMap K n h i) =
      (targetNode K).left.ker.comap (retainedComponent K).left := by
  have he := fiberIdeal_retained K n (by omega) p q hp i
  rw [componentι_normalization] at he
  exact he

/-- The stated normalization ideals determine the entire scheme-theoretic fiber uniquely. -/
theorem unique (I : (scheme K n h).IdealSheafData)
    (hI : ∀ j, j ≠ i → I.comap (componentMap K n h j) = ⊥)
    (hi : I.comap (componentMap K n h i) =
      (targetNode K).left.ker.comap (retainedComponent K).left) : I = F := by
  apply PolygonCollapsedIdealDetection.ideal_ext K n h i hI
    (fun _ hj ↦ component_omitted K n h i hj)
  rw [hi, component_retained]

/-- An interior node of the collapsed chain keeps the entire original nodal chart. -/
theorem interior_chart (j : Fin n) (hj : j ≠ i) (hs : finRotate n j ≠ i) :
    (F).comap (chart K n h j) = ⊥ := by
  apply PolygonNodeIdealSheafDetection.eq_bot K
  · rw [← Scheme.IdealSheafData.comap_comp, ← left_componentMap,
      Scheme.IdealSheafData.comap_comp, component_omitted K n h i hj,
      Scheme.IdealSheafData.comap_bot]
  · have he : secondBranch K ≫ chart K n h j =
        ProjectiveLine.right K ≫ componentMap K n h (finRotate n j) := by
      simp only [right_componentMap, Equiv.symm_apply_apply]
    rw [← Scheme.IdealSheafData.comap_comp, he,
      Scheme.IdealSheafData.comap_comp, component_omitted K n h i hs,
      Scheme.IdealSheafData.comap_bot]

end FLT.Mazur.PolygonCollapsedFiberIdeal
