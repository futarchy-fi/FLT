/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalInitialComponents
public import FLT.Mazur.WeierstrassDividedEqualityNodeFamily

/-!
# Initial component endpoints in the equality-depth family

Both complete initial components join their original initial section to the
first retained pair. These equations do not require strict depth inequality.
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

variable (s : ℕ) (hs : s + 1 ≤ n) (hstart : 0 < start)
  (hk : 2 * (start + s + 1) ≤ depth)
local notation "transport" => eqToHom
  (finiteGlobalTensorModel_index_congr hπ data K
    (a := 1 + s) (b := s + 1) (by omega) hs (by omega))

local notation "p" => pullback.fst (Spec.map (CommRingCat.ofHom (algebraMap R K)))
  (finiteGlobalStructure hπ data (s + 1) hs)

/-- The original complete initial component over the residue field. -/
def equalityInitialOverComponent (i : Fin 2) :
    PolygonPinching.component K ⟶ Over.mk p :=
  Over.homMk (finalInitialComponent hπ data D s hs hstart hk i)
    (finalInitialComponent_structure hπ data D s hs hstart hk i)

/-- Zero is the matching original initial node in the fixed final family. -/
@[reassoc] theorem equalityInitialOverComponent_zero (i : Fin 2) :
    ProjectiveLine.zeroSection K ≫ equalityInitialOverComponent hπ data D s hs hstart hk i =
      equalityNodeOverSection hπ data D s hs hk (.inl ⟨i, hstart⟩) := by
  apply Over.OverMorphism.ext
  change ProjectiveLine.zero K ≫ finalInitialComponent hπ data D s hs hstart hk i = _
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
@[reassoc] theorem equalityInitialOverComponent_infinity (i : Fin 2) :
    ProjectiveLine.infinitySection K ≫
      equalityInitialOverComponent hπ data D s hs hstart hk i =
      equalityNodeOverSection hπ data D s hs hk (.inr (0, i)) := by
  apply Over.OverMorphism.ext
  change ProjectiveLine.infinity K ≫ finalInitialComponent hπ data D s hs hstart hk i = _
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
