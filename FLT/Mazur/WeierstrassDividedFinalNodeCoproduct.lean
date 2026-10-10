/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedFinalNodeOrigins

/-!
# The actual indexed node leg over the residue field

Every original node is a section of the same coefficient structure. Their
coproduct gives the node leg for subsequent component cocone assembly.
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
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R K))

/-- Transported retained nodes remain actual residue-field sections. -/
@[reassoc] theorem retainedNodeSectionAt_structure (t : ℕ) (ht : t ≤ n)
    (j : ℕ) (hj : j + 1 ≤ t) (hk : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    retainedNodeSectionAt hπ data D t ht j hj hk i ≫
      pullback.fst q (finiteGlobalStructure hπ data t ht) = 𝟙 _ := by
  obtain ⟨r, he⟩ : ∃ r, t = j + 1 + r := ⟨t - (j + 1), by omega⟩
  subst t
  rw [retainedNodeSectionAt_original hπ data D j (by omega)]
  by_cases h : 0 < start + j
  · rw [orderedRetainedSection_positive hπ data D j (by omega) r ht hk h]
    fin_cases i
    · exact olderGlobalFirstSection_structure hπ data D j (by omega) r ht h hk
    · exact olderGlobalSecondSection_structure hπ data D j (by omega) r ht h hk
  · rw [orderedRetainedSection_zero hπ data D j (by omega) r ht hk (by omega)]
    fin_cases i
    · exact olderGlobalZeroFirstSection_structure hπ data D j (by omega) r ht (by omega) hk
    · exact olderGlobalZeroSecondSection_structure hπ data D j (by omega) r ht (by omega) hk

variable (s : ℕ) (hs : s + 1 ≤ n)
  (hk : 2 * (start + s + 1) ≤ depth) (hp : 2 * (start + s + 1) < depth)
local notation "p" => pullback.fst q (finiteGlobalStructure hπ data (s + 1) hs)

/-- All indexed nodes have the same original residue coefficient structure. -/
@[reassoc] theorem finalNodeSection_structure (i : FinalNodeIndex start s) :
    finalNodeSection hπ data D s hs hk hp i ≫ p = 𝟙 _ := by
  rcases i with (⟨a, ha⟩ | ⟨j, a⟩) | ⟨⟩
  · fin_cases a
    · exact initialGlobalFirstSection_structure hπ data D (s + 1) hs ha (by omega)
    · exact initialGlobalSecondSection_structure hπ data D (s + 1) hs ha (by omega)
  · exact retainedNodeSectionAt_structure hπ data D (s + 1) hs j.val (by omega) (by omega) a
  · change (PolygonNodePresentation.aOrigin K ≫
      terminalNodeChart hπ data D (s + 1) hs (by omega) hk hp) ≫ p = 𝟙 _
    rw [Category.assoc, terminalNodeChart_structure]
    exact PolygonCyclicAtlas.origin_toBase K

/-- The original node section as a morphism over the residue field. -/
def finalNodeOverSection (i : FinalNodeIndex start s) :
    PolygonPinching.point K ⟶ Over.mk p :=
  Over.homMk (finalNodeSection hπ data D s hs hk hp i)
    (finalNodeSection_structure hπ data D s hs hk hp i)

/-- The actual coproduct node leg, still indexed by the original node positions. -/
def finalNodeCoproductMap :
    (∐ fun _ : FinalNodeIndex start s => PolygonPinching.point K) ⟶ Over.mk p :=
  Sigma.desc (finalNodeOverSection hπ data D s hs hk hp)

/-- Each node summand maps by precisely the original section over the residue field. -/
@[reassoc] theorem finalNodeCoproductMap_ι (i : FinalNodeIndex start s) :
    Sigma.ι (fun _ : FinalNodeIndex start s => PolygonPinching.point K) i ≫
      finalNodeCoproductMap hπ data D s hs hk hp =
        finalNodeOverSection hπ data D s hs hk hp i := by
  exact Sigma.ι_comp_desc _ _

/-- Passing to schemes over the field does not identify any original node indices. -/
theorem finalNodeOverSection_injective :
    Function.Injective (finalNodeOverSection hπ data D s hs hk hp) := by
  intro a b he
  exact finalNodeSection_injective hπ data D s hs hk hp
    (congrArg (fun f => f.left) he)

end FLT.Mazur.WeierstrassDividedDepth
