/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialGlobalTensorChart
public import FLT.Mazur.WeierstrassModificationXResidueFullNodeGeometry

/-!
# Both initial residue nodes in the whole projective model

At positive initial depth the two full node neighborhoods cover precisely
the original initial tensor chart. The actual divided constant is retained.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j ≤ n)
  (hstart : 0 < start) (hk : 2 * start ≤ depth)
open WeierstrassModificationX
local notation "K" => ResidueField R
local notation "d₀" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d₀)
local notation "f" => residueFullFirstNodeChart D start hstart hk
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) (Data.factor3 d₀) (Data.factor4 d₀)
local notation "g" => residueFullSecondNodeChart D start hstart hk
  (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) (Data.factor3 d₀) (Data.factor4 d₀)
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- The first full initial node with its actual projective inclusion. -/
def initialGlobalResidueFirstNode :
    Spec (.of (FullNodeOpen a c)) ⟶ finiteGlobalTensorModel hπ data K j hj :=
  f ≫ globalInitialTensorChart hπ data K j hj

/-- The second full initial node with the opposite tangent orientation. -/
def initialGlobalResidueSecondNode :
    Spec (.of (FullNodeOpen (-a) c)) ⟶ finiteGlobalTensorModel hπ data K j hj :=
  g ≫ globalInitialTensorChart hπ data K j hj

instance initialGlobalResidueFirstNode_isOpenImmersion :
    IsOpenImmersion (initialGlobalResidueFirstNode hπ data D j hj hstart hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

instance initialGlobalResidueSecondNode_isOpenImmersion :
    IsOpenImmersion (initialGlobalResidueSecondNode hπ data D j hj hstart hk) :=
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- These two ordered nodes cover the entire original initial chart and no additional points. -/
theorem initialGlobalResidueNodes_range :
    Set.range (initialGlobalResidueFirstNode hπ data D j hj hstart hk) ∪
      Set.range (initialGlobalResidueSecondNode hπ data D j hj hstart hk) =
        Set.range (globalInitialTensorChart hπ data K j hj) := by
  ext z
  constructor
  · rintro (⟨x, rfl⟩ | ⟨x, rfl⟩)
    · exact ⟨(f) x, rfl⟩
    · exact ⟨(g) x, rfl⟩
  · rintro ⟨x, rfl⟩
    rcases residue_fullNodeCharts_cover D start hstart hk
      (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀) (Data.factor3 d₀) (Data.factor4 d₀) x with
      ⟨t, ht⟩ | ⟨t, ht⟩
    · exact Or.inl ⟨t, congrArg (globalInitialTensorChart hπ data K j hj) ht⟩
    · exact Or.inr ⟨t, congrArg (globalInitialTensorChart hπ data K j hj) ht⟩

/-- The first initial node retains the whole original cubic contraction. -/
theorem initialGlobalResidueFirstNode_toCurve :
    initialGlobalResidueFirstNode hπ data D j hj hstart hk ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj =
      fullFirstNodeChart a c (residue_tangent_isUnit D) ≫
        residueFullContraction D start hstart hk (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
          (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀) := by
  rw [initialGlobalResidueFirstNode, Category.assoc, globalInitialTensorChart_toCurve]
  exact residueFullFirstNodeChart_contraction D start hstart hk
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
    (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀)

/-- The second initial node retains that same complete original contraction. -/
theorem initialGlobalResidueSecondNode_toCurve :
    initialGlobalResidueSecondNode hπ data D j hj hstart hk ≫
      pullback.snd q (finiteGlobalStructure hπ data j hj) ≫
        finiteGlobalContraction hπ data j hj =
      fullSecondNodeChart a c (residue_tangent_isUnit D) ≫
        residueFullContraction D start hstart hk (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
          (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀) := by
  rw [initialGlobalResidueSecondNode, Category.assoc, globalInitialTensorChart_toCurve]
  exact residueFullSecondNodeChart_contraction D start hstart hk
    (Data.b3 d₀) (Data.b4 d₀) (Data.b6 d₀)
    (Data.factor3 d₀) (Data.factor4 d₀) (Data.factor6 d₀)

end FLT.Mazur.WeierstrassDividedDepth
