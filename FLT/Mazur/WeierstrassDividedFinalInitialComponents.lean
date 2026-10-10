/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialComponentStructure
public import FLT.Mazur.WeierstrassDividedFinalAdjacentComponents

/-!
# Both initial projective components in the fixed final node family

Only the presentation of the target stage is changed. Each zero is the original
initial node, and each infinity is the first ordered retained node.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- Index transport preserves the complete first original initial section. -/
@[reassoc] theorem initialGlobalFirstSection_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b)
    (hstart : 0 < start) (hk : 2 * start ≤ depth) :
    initialGlobalFirstSection hπ data D a ha hstart hk ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      initialGlobalFirstSection hπ data D b hb hstart hk := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

/-- Index transport preserves the complete opposite original initial section. -/
@[reassoc] theorem initialGlobalSecondSection_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b)
    (hstart : 0 < start) (hk : 2 * start ≤ depth) :
    initialGlobalSecondSection hπ data D a ha hstart hk ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      initialGlobalSecondSection hπ data D b hb hstart hk := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

variable (s : ℕ) (hs : s + 1 ≤ n) (hstart : 0 < start)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "transport" => eqToHom
  (finiteGlobalTensorModel_index_congr hπ data K
    (a := 1 + s) (b := s + 1) (by omega) hs (by omega))

/-- The two complete initial components in the fixed final model, in original tangent order. -/
def finalInitialComponent (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (s + 1) hs :=
  Fin.cases (initialGlobalFirstComponent hπ data D (by omega) hstart (by omega) s (by omega))
    (fun _ => initialGlobalSecondComponent hπ data D (by omega) hstart (by omega) s (by omega))
    i ≫ transport

/-- Both initial projective components retain their original residue-field structure. -/
@[reassoc] theorem finalInitialComponent_structure (i : Fin 2) :
    finalInitialComponent hπ data D s hs hstart hk i ≫
        pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          (finiteGlobalStructure hπ data (s + 1) hs) = ProjectiveLine.toBase K := by
  rw [finalInitialComponent, Category.assoc,
    finiteGlobalTensorModel_structure_transport hπ data K _ hs (by omega)]
  fin_cases i
  · exact initialGlobalFirstComponent_structure hπ data D _ hstart _ s _
  · exact initialGlobalSecondComponent_structure hπ data D _ hstart _ s _

variable (hp : 2 * (start + s + 1) < depth)

/-- Zero is the matching original initial node in the fixed final family. -/
@[reassoc] theorem finalInitialComponent_zero (i : Fin 2) :
    ProjectiveLine.zero K ≫ finalInitialComponent hπ data D s hs hstart hk i =
      finalNodeSection hπ data D s hs hk hp (.inl (.inl ⟨i, hstart⟩)) := by
  rw [finalInitialComponent, ← Category.assoc]
  fin_cases i
  · change (ProjectiveLine.zero K ≫
        initialGlobalFirstComponent hπ data D (by omega) hstart (by omega) s (by omega)) ≫
          transport = _
    rw [initialGlobalFirstComponent_zero,
      initialGlobalFirstSection_index_transport hπ data D _ hs (by omega)]
    rfl
  · change (ProjectiveLine.zero K ≫
        initialGlobalSecondComponent hπ data D (by omega) hstart (by omega) s (by omega)) ≫
          transport = _
    rw [initialGlobalSecondComponent_zero,
      initialGlobalSecondSection_index_transport hπ data D _ hs (by omega)]
    rfl

/-- Infinity is the matching first retained node in the same fixed family. -/
@[reassoc] theorem finalInitialComponent_infinity (i : Fin 2) :
    ProjectiveLine.infinity K ≫ finalInitialComponent hπ data D s hs hstart hk i =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (0, i))) := by
  have H : orderedRetainedSection hπ data D 0 (by omega) s (by omega) (by omega) i ≫
      transport = retainedNodeSectionAt hπ data D (s + 1) hs 0 (by omega) (by omega) i := by
    rw [← retainedNodeSectionAt_original hπ data D 0 (by omega) s (by omega) (by omega),
      retainedNodeSectionAt_index_transport hπ data D _ hs (by omega)]
  rw [orderedRetainedSection_positive hπ data D 0 (by omega) s (by omega)
    (by omega) hstart] at H
  rw [finalInitialComponent, ← Category.assoc]
  fin_cases i
  · change (ProjectiveLine.infinity K ≫
        initialGlobalFirstComponent hπ data D (by omega) hstart (by omega) s (by omega)) ≫
          transport = _
    rw [initialGlobalFirstComponent_infinity]
    exact H
  · change (ProjectiveLine.infinity K ≫
        initialGlobalSecondComponent hπ data D (by omega) hstart (by omega) s (by omega)) ≫
          transport = _
    rw [initialGlobalSecondComponent_infinity]
    exact H

end FLT.Mazur.WeierstrassDividedDepth
