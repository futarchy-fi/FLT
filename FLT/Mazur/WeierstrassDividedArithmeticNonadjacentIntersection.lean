/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNilpotentNonadjacentIntersection
public import FLT.Mazur.WeierstrassDividedArithmeticBoundaryCharts

/-!
# Empty nonadjacent intersections in every original arithmetic stage

The full indexed global charts remain disjoint after extension to R/(π^(m+1)).
Both actual maps land in the original arithmetic stage, at their retained indices.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open PolygonArithmeticStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] finiteGlobalModel finiteGlobalContraction
variable {R : Type} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (m : ℕ)
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n) (i : Fin (j + 1))
local notation "Q" => Quotient R π m
local notation "q" => Spec.map (CommRingCat.ofHom (algebraMap R Q))
local notation "old" => globalTensorAtlasMap hπ data Q (j + 2 + r) hr
  (Fin.succ (Fin.mk (i.val + 2 + r + 1) (by omega)))
local notation "new" => globalTensorAtlasMap hπ data Q (j + 2 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))
local notation "E" => pullbackSymmetry q (finiteGlobalStructure hπ data (j + 2 + r) hr)

include hj hjNext in
/-- Nonadjacent full indexed charts have empty intersection in the actual arithmetic stage. -/
theorem nonadjacentArithmeticTensorAtlas_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) (old ≫ (E).hom) (new ≫ (E).hom) := by
  have hp : IsNilpotent (algebraMap R Q π) := ⟨m + 1, parameter_pow R π m⟩
  have H := nonadjacentGlobalTensorAtlas_nilpotent_isPullback
    hπ data Q j hj hjNext r hr hp i
  exact IsPullback.of_isLimit
    (PullbackCone.isLimitOfCompMono _ _ (E).hom H.cone H.isLimit)

include hj hjNext in
/-- Full nonadjacent global chart images are disjoint at every arithmetic quotient order. -/
theorem nonadjacentArithmeticTensorAtlas_disjoint :
    Disjoint (Set.range (old ≫ (E).hom)) (Set.range (new ≫ (E).hom)) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨z, _, _⟩ := Scheme.exists_preimage_of_isPullback
    (nonadjacentArithmeticTensorAtlas_isPullback hπ data m j hj hjNext r hr i) a b hb.symm
  exact isEmptyElim z

/-- The empty comparison is with the entire actual arithmetic fiber product. -/
def nonadjacentArithmeticTensorPullbackIso :
    (∅ : Scheme) ≅ pullback (old ≫ (E).hom) (new ≫ (E).hom) :=
  (nonadjacentArithmeticTensorAtlas_isPullback hπ data m j hj hjNext r hr i).isoPullback

end FLT.Mazur.WeierstrassDividedDepth
