/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialIndexedNodeCover
public import FLT.Mazur.WeierstrassDividedResidueAtlasFinite

/-!
# A finite global residue cover including the two initial nodes

Refine the remaining initial ModificationX index by its own ordered nodes.
All older node refinements, the terminal parity form, and infinity are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (s : ℕ) (hs : s ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + s) ≤ depth)
local notation "K" => ResidueField R

/-- Transport the constructed initial node cover to any spelling of its exact index. -/
def initialIndexedNodeCoverAt (i : Fin (s + 3)) (hi : i.val = s + 2) :
    (globalTensorAtlasObject hπ data K s hs i).OpenCover := by
  have hi' : i = Fin.succ ⟨s + 1, by clear i hi; omega⟩ := Fin.ext hi
  subst i
  exact initialIndexedNodeOpenCover hπ data D s hs hstart (by omega)

instance initialIndexedNodeCoverAt_finite (i : Fin (s + 3)) (hi : i.val = s + 2) :
    Finite (initialIndexedNodeCoverAt hπ data D s hs hstart hk i hi).I₀ := by
  have hi' : i = Fin.succ ⟨s + 1, by clear i hi; omega⟩ := Fin.ext hi
  subst i
  exact inferInstanceAs (Finite (Fin 2))

/-- Simultaneously refine every finite-depth chart, including the separate initial chart. -/
def globalInitialResidueAtlasRefinement (i : Fin (s + 3)) :
    (globalTensorAtlasObject hπ data K s hs i).OpenCover := by
  classical
  exact if hi : i.val = s + 2 then
    initialIndexedNodeCoverAt hπ data D s hs hstart hk i hi
  else globalResidueAtlasRefinement hπ data D s hs hstart hk i

instance globalInitialResidueAtlasRefinement_finite (i : Fin (s + 3)) :
    Finite (globalInitialResidueAtlasRefinement hπ data D s hs hstart hk i).I₀ := by
  classical
  unfold globalInitialResidueAtlasRefinement
  split_ifs <;> infer_instance

/-- These actual normalized charts still cover the entire projective residue model. -/
def globalInitialResidueOpenCover : (finiteGlobalTensorModel hπ data K s hs).OpenCover :=
  (globalTensorOpenCover hπ data K s hs).bind
    (globalInitialResidueAtlasRefinement hπ data D s hs hstart hk)

instance globalInitialResidueOpenCover_finite :
    Finite (globalInitialResidueOpenCover hπ data D s hs hstart hk).I₀ := by
  change Finite ((i : Fin (s + 3)) ×
    (globalInitialResidueAtlasRefinement hπ data D s hs hstart hk i).I₀)
  infer_instance

/-- Each member retains its actual original global atlas inclusion. -/
theorem globalInitialResidueOpenCover_map (i : Fin (s + 3))
    (a : (globalInitialResidueAtlasRefinement hπ data D s hs hstart hk i).I₀) :
    (globalInitialResidueOpenCover hπ data D s hs hstart hk).f ⟨i, a⟩ =
      (globalInitialResidueAtlasRefinement hπ data D s hs hstart hk i).f a ≫
        globalTensorAtlasMap hπ data K s hs i := rfl

/-- Every global point lies in one of the retained or normalized charts. -/
theorem globalInitialResidueOpenCover_covers (z : finiteGlobalTensorModel hπ data K s hs) :
    ∃ i x, (globalInitialResidueOpenCover hπ data D s hs hstart hk).f i x = z :=
  (globalInitialResidueOpenCover hπ data D s hs hstart hk).exists_eq z

end FLT.Mazur.WeierstrassDividedDepth
