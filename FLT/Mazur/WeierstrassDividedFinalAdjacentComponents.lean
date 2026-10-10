/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOrderedAdjacentComponents

/-!
# All adjacent projective components in the fixed final stage

Only the natural-number target index is transported. Both endpoints remain
exactly the original ordered retained sections in the fixed node family.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth)
local notation "K" => ResidueField R

/-- Rewriting a stage index preserves the entire retained node section. -/
@[reassoc] theorem retainedNodeSectionAt_index_transport {a b : ℕ}
    (ha : a ≤ n) (hb : b ≤ n) (he : a = b)
    (j : ℕ) (hj : j + 1 ≤ a) (hdepth : 2 * (start + j + 1) ≤ depth) (i : Fin 2) :
    retainedNodeSectionAt hπ data D a ha j hj hdepth i ≫
        eqToHom (finiteGlobalTensorModel_index_congr hπ data K ha hb he) =
      retainedNodeSectionAt hπ data D b hb j (by omega) hdepth i := by
  subst b
  simp only [eqToHom_refl, Category.comp_id]

variable (s : ℕ) (hs : s + 1 ≤ n) (hk : 2 * (start + s + 1) ≤ depth)

/-- The complete component between retained levels j and j+1 at the final stage. -/
def finalAdjacentComponent (j : Fin s) (i : Fin 2) :
    ProjectiveLine.scheme K ⟶ finiteGlobalTensorModel hπ data K (s + 1) hs :=
  orderedAdjacentComponent hπ data D j.val (by omega) (by omega) (by omega) (by omega)
    (s - (j.val + 1)) (by omega) i ≫
      eqToHom (finiteGlobalTensorModel_index_congr hπ data K (by omega) hs (by omega))

/-- Expressing the final stage as an adjacent stage recovers the full original component. -/
theorem finalAdjacentComponent_original (j r : ℕ) (hr : j + 2 + r ≤ n)
    (hdepth : 2 * (start + (j + 1 + r) + 1) ≤ depth) (i : Fin 2) :
    HEq (finalAdjacentComponent hπ data D (j + 1 + r) (by omega) hdepth ⟨j, by omega⟩ i)
      (orderedAdjacentComponent hπ data D j (by omega) (by omega) (by omega) (by omega)
        r hr i) := by
  refine (comp_eqToHom_heq _ _).trans ?_
  congr 1
  · change j + 1 + r - (j + 1) = r
    omega
  · apply proof_irrel_heq

variable (hp : 2 * (start + s + 1) < depth)

/-- Zero retains the preceding ordered node in the fixed family. -/
@[reassoc] theorem finalAdjacentComponent_zero (j : Fin s) (i : Fin 2) :
    ProjectiveLine.zero K ≫ finalAdjacentComponent hπ data D s hs hk j i =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (⟨j.val, by omega⟩, i))) := by
  rw [finalAdjacentComponent, ← Category.assoc, orderedAdjacentComponent_zero,
    retainedNodeSectionAt_index_transport hπ data D _ _ (by omega)]
  rfl

/-- Infinity retains the matching next ordered node in the fixed family. -/
@[reassoc] theorem finalAdjacentComponent_infinity (j : Fin s) (i : Fin 2) :
    ProjectiveLine.infinity K ≫ finalAdjacentComponent hπ data D s hs hk j i =
      finalNodeSection hπ data D s hs hk hp (.inl (.inr (⟨j.val + 1, by omega⟩, i))) := by
  rw [finalAdjacentComponent, ← Category.assoc, orderedAdjacentComponent_infinity,
    retainedNodeSectionAt_index_transport hπ data D _ _ (by omega)]
  rfl

end FLT.Mazur.WeierstrassDividedDepth
