/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedNonadjacentTensorIntersection

/-!
# Non-adjacent special-fiber intersections in the global atlas

The actual global open embedding preserves the empty intersections between
all non-adjacent indexed successive charts, including the initial exterior.
Both projections of each full categorical intersection are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [CommRing S] [Algebra R S]
  (j : ℕ) (hj : j + 1 ≤ n) (hjNext : j + 2 ≤ n)
  (r : ℕ) (hr : j + 2 + r ≤ n)
  (i : Fin (j + 1)) (hp : algebraMap R S π = 0)
local notation "old" => globalTensorAtlasMap hπ data S (j + 2 + r) hr
  (Fin.succ (Fin.mk (i.val + 2 + r + 1) (by omega)))
local notation "new" => globalTensorAtlasMap hπ data S (j + 2 + r) hr
  (Fin.succ (Fin.mk (r + 1) (by omega)))

include hj hjNext hp

/-- Globalization retains the entire empty non-adjacent special-fiber intersection. -/
theorem nonadjacentGlobalTensorAtlas_isPullback :
    IsPullback (Scheme.emptyTo _) (Scheme.emptyTo _) old new := by
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _
    (finiteLocalTensorEmbedding hπ data S (j + 2 + r) hr)
    (nonadjacentTensorAtlas_isPullback hπ data S j hj hjNext r hr i hp).cone
    (nonadjacentTensorAtlas_isPullback hπ data S j hj hjNext r hr i hp).isLimit)

/-- The non-adjacent original chart images remain disjoint in the actual global model. -/
theorem nonadjacentGlobalTensorAtlas_disjoint :
    Disjoint (Set.range old) (Set.range new) := by
  rw [Set.disjoint_left]
  rintro _ ⟨a, rfl⟩ ⟨b, hb⟩
  obtain ⟨z, _, _⟩ := Scheme.exists_preimage_of_isPullback
    (nonadjacentGlobalTensorAtlas_isPullback hπ data S j hj hjNext r hr i hp) a b hb.symm
  exact isEmptyElim z

/-- The full global non-adjacent fiber product is canonically the empty scheme. -/
def nonadjacentGlobalTensorPullbackIso : (∅ : Scheme) ≅ pullback old new :=
  (nonadjacentGlobalTensorAtlas_isPullback hπ data S j hj hjNext r hr i hp).isoPullback

/-- The empty comparison retains the actual older atlas projection. -/
@[reassoc] theorem nonadjacentGlobalTensorPullbackIso_old :
    (nonadjacentGlobalTensorPullbackIso hπ data S j hj hjNext r hr i hp).hom ≫
      pullback.fst old new = Scheme.emptyTo _ :=
  (nonadjacentGlobalTensorAtlas_isPullback hπ data S j hj hjNext r hr i hp).isoPullback_hom_fst

/-- The empty comparison retains the actual newer atlas projection. -/
@[reassoc] theorem nonadjacentGlobalTensorPullbackIso_new :
    (nonadjacentGlobalTensorPullbackIso hπ data S j hj hjNext r hr i hp).hom ≫
      pullback.snd old new = Scheme.emptyTo _ :=
  (nonadjacentGlobalTensorAtlas_isPullback hπ data S j hj hjNext r hr i hp).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
