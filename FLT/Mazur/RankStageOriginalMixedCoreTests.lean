/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealSheafClosedCoreTests
public import FLT.Mazur.RankStageOriginalMixedTests

/-!
# Canonical tests in the entire rank-core relation

Original mixed coordinates whose first endpoint lies in the core induce full
core-relation tests. Invariance of the core retains the second endpoint, so
both original-source squares are consequences of the construction.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [Etale q] [IsLocallyNoetherian A] [IsAffine A]
  [LocallyQuasiFinite p] (e : CategoryTheory.EquivalenceRelation p q)
local instance mixedCoreTestOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance mixedCoreTestOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance mixedCoreTestOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
variable (n : ℕ) (a : Γ(A, ⊤)) (ha : A.basicOpen a ≤ rankImageOpen (Over.mk p) n)
  (b : Γ(A, ⊤)) (hb : A.basicOpen b ≤ rankImageOpen (Over.mk p) n) (k : ℕ)
set_option quotPrecheck false
local notation "X" => (rankImageOpen (Over.mk p) n).toScheme
local notation "I" => rankStratumIdeal (Over.mk p) n
local notation "C" => rankStageCore e n a ha k
local notation "U" => rankStageOriginalAffineOpen (p := p) n b hb
attribute [local irreducible] rankStageCore



variable (h : rankThickeningMap (Over.mk p) n k ⁻¹ᵁ A.basicOpen b ≤
    rankStageCore e n a ha k)
  {T : Scheme.{0}} (g g' : T ⟶ (rankImageOpen (Over.mk p) n).toScheme)
  (hg : ⊤ ≤ g ⁻¹ᵁ (rankStageOriginalAffineOpen (p := p) n b hb).1)
  (δ : T ⟶ D) (hδ : δ ≫ p = g ≫ (rankImageOpen (Over.mk p) n).ι)
  (hδ' : δ ≫ q = g' ≫ (rankImageOpen (Over.mk p) n).ι)
local notation "K" => (I).comap g
local notation "r" => rankStageFirst (p := p) n k
local notation "s" => rankStageSecond e n k
local notation "z" => rankStageOriginalMixedTest n k g δ hδ

include h hg in
/-- The full mixed test factors through the entire first preimage of the core. -/
theorem rankStageOriginalMixedTest_core_domain : ⊤ ≤ z ⁻¹ᵁ (r ⁻¹ᵁ C) := by
  change ⊤ ≤ (z ≫ r) ⁻¹ᵁ C
  rw [rankStageOriginalMixedTest_first]
  exact IdealSheafClosedCoreTests.pulledMap_domain I (k + 1) U C h g hg

/-- The canonical full core-relation test of an original mixed coordinate. -/
def rankStageOriginalMixedCoreTest : (K ^ (k + 1)).subscheme ⟶ (r ⁻¹ᵁ C).toScheme :=
  IdealSheafClosedCoreTests.openLift (r ⁻¹ᵁ C) z
    (rankStageOriginalMixedTest_core_domain e n a ha b hb k h g hg δ hδ)

/-- The first core endpoint has the unchanged original source square. -/
@[reassoc]
theorem rankStageOriginalMixedCoreTest_first :
    (rankStageOriginalMixedCoreTest e n a ha b hb k h g hg δ hδ ≫
      (r).resLE C _ le_rfl) ≫ (C).ι ≫ (I ^ (k + 1)).subschemeι =
        (K ^ (k + 1)).subschemeι ≫ g := by
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι_assoc]
  rw [rankStageOriginalMixedCoreTest, IdealSheafClosedCoreTests.openLift_inclusion_assoc,
    rankStageOriginalMixedTest_first_assoc, IdealSheafAffineTestErrors.pulledMap_inclusion]

include hδ' in
/-- The second core endpoint retains the independently chosen original source map. -/
@[reassoc]
theorem rankStageOriginalMixedCoreTest_second :
    (rankStageOriginalMixedCoreTest e n a ha b hb k h g hg δ hδ ≫
      (s).resLE C _ (rankStageCore_invariant e n a ha k).le) ≫
        (C).ι ≫ (I ^ (k + 1)).subschemeι = (K ^ (k + 1)).subschemeι ≫ g' := by
  simp only [Category.assoc, Scheme.Hom.resLE_comp_ι_assoc]
  rw [rankStageOriginalMixedCoreTest, IdealSheafClosedCoreTests.openLift_inclusion_assoc]
  exact rankStageOriginalMixedTest_second e n k g g' δ hδ hδ'

end FLT.Mazur.EquivalenceRelationOrderedFrames
