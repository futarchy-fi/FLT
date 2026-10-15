/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedLocalComponentContraction
public import FLT.Mazur.WeierstrassDividedAdjacentComponentRanges
public import FLT.Mazur.WeierstrassDividedFinalAdjacentComponents

/-!
# Every complete adjacent exceptional component has constant cubic contraction

Both original affine pieces lie in the actual local modification. Affine
rigidity therefore computes the whole contraction from its original endpoint,
including both tangent branches at scale one and every later retained stage.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteLocalTensorEmbedding
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (hk : 2 * (start + j + 1) ≤ depth)
  (hjNext : j + 2 ≤ n) (hkNext : 2 * (start + (j + 1) + 1) ≤ depth)
  (r : ℕ) (hr : j + 2 + r ≤ n)
local notation "K" => ResidueField R
local notation "e" => finiteLocalTensorEmbedding hπ data K (j + 2 + r) hr

/-- The first retained adjacent line lies entirely in the actual local model. -/
theorem adjacentRetainedFirstComponent_range_local (hk0 : 0 < start + j) :
    Set.range (adjacentRetainedFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr) ⊆
      Set.range e := by
  rw [adjacentRetainedFirstComponent_range]
  rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> exact ⟨_, rfl⟩

/-- The second retained adjacent line has the same original local factorization. -/
theorem adjacentRetainedSecondComponent_range_local (hk0 : 0 < start + j) :
    Set.range (adjacentRetainedSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr) ⊆
      Set.range e := by
  rw [adjacentRetainedSecondComponent_range]
  rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> exact ⟨_, rfl⟩

/-- The first scale-one adjacent line also lies in the full original local model. -/
theorem adjacentZeroFirstComponent_range_local (hk0 : start + j = 0) :
    Set.range (adjacentZeroFirstComponent hπ data D j hj hk0 hk hjNext hkNext r hr) ⊆
      Set.range e := by
  rw [adjacentZeroFirstComponent_range]
  rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> exact ⟨_, rfl⟩

/-- The opposite scale-one adjacent line retains its entire local factorization. -/
theorem adjacentZeroSecondComponent_range_local (hk0 : start + j = 0) :
    Set.range (adjacentZeroSecondComponent hπ data D j hj hk0 hk hjNext hkNext r hr) ⊆
      Set.range e := by
  rw [adjacentZeroSecondComponent_range]
  rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> exact ⟨_, rfl⟩

/-- Either ordered adjacent component is wholly contained in the original local open. -/
theorem orderedAdjacentComponent_range_local (i : Fin 2) :
    Set.range (orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr i) ⊆
      Set.range e := by
  by_cases h : 0 < start + j
  · rw [orderedAdjacentComponent_positive hπ data D j hj hk hjNext hkNext r hr h]
    fin_cases i
    · exact adjacentRetainedFirstComponent_range_local hπ data D j hj hk hjNext hkNext r hr h
    · exact adjacentRetainedSecondComponent_range_local hπ data D j hj hk hjNext hkNext r hr h
  · have h0 : start + j = 0 := by omega
    rw [orderedAdjacentComponent_zero_depth hπ data D j hj hk hjNext hkNext r hr h0]
    fin_cases i
    · exact adjacentZeroFirstComponent_range_local hπ data D j hj hk hjNext hkNext r hr h0
    · exact adjacentZeroSecondComponent_range_local hπ data D j hj hk hjNext hkNext r hr h0

/-- The full original contraction of an adjacent component is its original zero endpoint value. -/
theorem orderedAdjacentComponent_contraction_constant (i : Fin 2) :
    orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr i ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          (finiteGlobalStructure hπ data (j + 2 + r) hr) ≫
            finiteGlobalContraction hπ data (j + 2 + r) hr =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫
        orderedAdjacentComponent hπ data D j hj hk hjNext hkNext r hr i ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R K)))
            (finiteGlobalStructure hπ data (j + 2 + r) hr) ≫
              finiteGlobalContraction hπ data (j + 2 + r) hr :=
  projectiveComponent_contraction_constant_of_range hπ data (j + 2 + r) hr K _
    (orderedAdjacentComponent_range_local hπ data D j hj hk hjNext hkNext r hr i)

/-- Transport to the fixed final stage preserves constancy of the entire adjacent contraction. -/
theorem finalAdjacentComponent_contraction_constant (s : ℕ) (hs : s + 1 ≤ n)
    (hdepth : 2 * (start + s + 1) ≤ depth) (k : Fin s) (i : Fin 2) :
    finalAdjacentComponent hπ data D s hs hdepth k i ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          (finiteGlobalStructure hπ data (s + 1) hs) ≫
            finiteGlobalContraction hπ data (s + 1) hs =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫
        finalAdjacentComponent hπ data D s hs hdepth k i ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R K)))
            (finiteGlobalStructure hπ data (s + 1) hs) ≫
              finiteGlobalContraction hπ data (s + 1) hs := by
  simp only [finalAdjacentComponent, Category.assoc]
  rw [finiteGlobalTensorModel_cubic_transport hπ data K _ _ (by omega)]
  exact orderedAdjacentComponent_contraction_constant hπ data D k.val (by omega)
    (by omega) (by omega) (by omega) (s - (k.val + 1)) (by omega) i

end FLT.Mazur.WeierstrassDividedDepth
