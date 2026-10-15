/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedLocalComponentContraction
public import FLT.Mazur.WeierstrassDividedTerminalComponentRanges
public import FLT.Mazur.WeierstrassDividedFinalTerminalComponents

/-!
# Both complete terminal components contract to their original endpoint

Every affine piece of either terminal projective line belongs to the actual
local modification. Its original cubic contraction is therefore constant,
including the scale-one terminal pair.
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
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) < depth)
local notation "K" => ResidueField R
local notation "e" => finiteLocalTensorEmbedding hπ data K (j + 1) hj

/-- Both affine pieces of the first positive-scale terminal component lie in the local model. -/
theorem terminalFirstComponent_range_local (hk0 : 0 < start + j) :
    Set.range (terminalFirstComponent hπ data D j hj hk0 hk hp) ⊆ Set.range e := by
  rw [terminalFirstComponent_range]
  rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> exact ⟨_, rfl⟩

/-- The opposite positive-scale terminal component likewise belongs to the entire local model. -/
theorem terminalSecondComponent_range_local (hk0 : 0 < start + j) :
    Set.range (terminalSecondComponent hπ data D j hj hk0 hk hp) ⊆ Set.range e := by
  rw [terminalSecondComponent_range]
  rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> exact ⟨_, rfl⟩

/-- The first scale-one terminal component also lies in the actual local modification. -/
theorem terminalZeroFirstComponent_range_local (hk0 : start + j = 0) :
    Set.range (terminalZeroFirstComponent hπ data D j hj hk0 hk hp) ⊆ Set.range e := by
  rw [terminalZeroFirstComponent_range]
  rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> exact ⟨_, rfl⟩

/-- The opposite scale-one terminal component retains the same local factorization. -/
theorem terminalZeroSecondComponent_range_local (hk0 : start + j = 0) :
    Set.range (terminalZeroSecondComponent hπ data D j hj hk0 hk hp) ⊆ Set.range e := by
  rw [terminalZeroSecondComponent_range]
  rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩) <;> exact ⟨_, rfl⟩

/-- Each ordered complete terminal component is contained in the original local open. -/
theorem finalTerminalComponent_range_local (i : Fin 2) :
    Set.range (finalTerminalComponent hπ data D j hj hk hp i) ⊆ Set.range e := by
  by_cases h : 0 < start + j
  · rw [finalTerminalComponent_positive hπ data D j hj hk hp h]
    fin_cases i
    · exact terminalFirstComponent_range_local hπ data D j hj hk hp h
    · exact terminalSecondComponent_range_local hπ data D j hj hk hp h
  · have h0 : start + j = 0 := by omega
    rw [finalTerminalComponent_zero_depth hπ data D j hj hk hp h0]
    fin_cases i
    · exact terminalZeroFirstComponent_range_local hπ data D j hj hk hp h0
    · exact terminalZeroSecondComponent_range_local hπ data D j hj hk hp h0

/-- The original cubic contraction of either entire terminal component is its endpoint value. -/
theorem finalTerminalComponent_contraction_constant (i : Fin 2) :
    finalTerminalComponent hπ data D j hj hk hp i ≫
        pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R K)))
          (finiteGlobalStructure hπ data (j + 1) hj) ≫
            finiteGlobalContraction hπ data (j + 1) hj =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫
        finalTerminalComponent hπ data D j hj hk hp i ≫
          pullback.snd (Spec.map (CommRingCat.ofHom (algebraMap R K)))
            (finiteGlobalStructure hπ data (j + 1) hj) ≫
              finiteGlobalContraction hπ data (j + 1) hj :=
  projectiveComponent_contraction_constant_of_range hπ data (j + 1) hj K _
    (finalTerminalComponent_range_local hπ data D j hj hk hp i)

end FLT.Mazur.WeierstrassDividedDepth
