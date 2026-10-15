/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedLocalComponentContraction
public import FLT.Mazur.WeierstrassDividedEqualityComponentEndpoints

/-!
# The complete equality-depth terminal component has constant cubic contraction

The entire conic and Laurent pieces belong to the original local modification.
Their complete projective gluing therefore contracts to its actual endpoint,
including the depth-two case.
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
  (hk : 2 * (start + j + 1) ≤ depth) (hp : 2 * (start + j + 1) = depth)
local notation "K" => ResidueField R
local notation "e" => finiteLocalTensorEmbedding hπ data K (j + 1) hj
local notation "T" => laurentTerminalProjectiveComponent hπ data D j hj hk hp
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))
local notation "f" => finiteGlobalStructure hπ data (j + 1) hj
local notation "g" => finiteGlobalContraction hπ data (j + 1) hj

/-- The complete equality-depth projective component lies in the original local modification. -/
theorem laurentTerminalProjectiveComponent_range_local : Set.range T ⊆ Set.range e := by
  rw [laurentTerminalProjectiveComponent_range]
  rintro y (⟨x, rfl⟩ | ⟨x, rfl⟩)
  · by_cases h : 0 < start + j
    · rw [laurentTerminalOriginalConic_positive hπ data D j hj hk h]
      exact ⟨_, rfl⟩
    · rw [laurentTerminalOriginalConic_zero hπ data D j hj hk (by omega)]
      exact ⟨_, rfl⟩
  · exact ⟨_, rfl⟩

/-- The whole equality-depth terminal component contracts to its original zero attachment. -/
theorem laurentTerminalProjectiveComponent_contraction_constant :
    T ≫ pullback.snd q f ≫ g =
      ProjectiveLine.toBase K ≫ ProjectiveLine.zero K ≫ T ≫ pullback.snd q f ≫ g :=
  projectiveComponent_contraction_constant_of_range hπ data (j + 1) hj K _
    (laurentTerminalProjectiveComponent_range_local hπ data D j hj hk hp)

/-- The two original attachment sections have equal original cubic contractions. -/
theorem laurentTerminalProjectiveComponent_contraction_endpoints :
    ProjectiveLine.zero K ≫ T ≫ pullback.snd q f ≫ g =
      ProjectiveLine.infinity K ≫ T ≫ pullback.snd q f ≫ g := by
  conv_rhs => rw [laurentTerminalProjectiveComponent_contraction_constant]
  rw [ProjectiveLine.infinity_toBase_assoc]

end FLT.Mazur.WeierstrassDividedDepth
