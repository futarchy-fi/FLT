/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalMiddleComponents
public import FLT.Mazur.WeierstrassModificationXConicOverlapGeometry

/-!
# The full conic parameter overlap in the retained global fiber

The explicit double localization remains the actual intersection after the
conic is embedded in the retained global model. Both parameter projections
keep their ordering and their exact global morphisms.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassModificationX
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)

local notation "a" => residue R W.a₁
local notation "ha" => D.a₁_unit.map (residue R)
local notation "C" => olderGlobalMiddleConic hπ data D j hj r hr hk0 hk
local notation "P₁" => olderGlobalMiddleConicFirstParameter hπ data D j hj r hr hk0 hk
local notation "P₂" => olderGlobalMiddleConicSecondParameter hπ data D j hj r hr hk0 hk
local notation "l" => conicOverlapFirstParameterMap a c ha
local notation "r₀" => conicOverlapSecondParameterMap a c ha

instance olderGlobalMiddleConic_mono : Mono C :=
  inferInstanceAs (Mono (_ ≫ _))

/-- The original double localization is exactly the global parameter intersection. -/
theorem olderGlobalConicOverlap_isPullback : IsPullback l r₀ P₁ P₂ := by
  have h := conicParameterOverlap_isPullback a c ha
  exact IsPullback.of_isLimit (PullbackCone.isLimitOfCompMono _ _ C h.cone h.isLimit)

/-- The actual conic overlap map to the retained global fiber. -/
def olderGlobalConicOverlap := l ≫ P₁

/-- The second overlap projection gives the same global map, with its order retained. -/
@[reassoc] theorem olderGlobalConicOverlap_second :
    r₀ ≫ P₂ = olderGlobalConicOverlap hπ data D j hj r hr hk0 hk :=
  (olderGlobalConicOverlap_isPullback hπ data D j hj r hr hk0 hk).w.symm

/-- The full global parameter overlap is the explicitly constructed double localization. -/
def olderGlobalConicOverlapIso : Spec (.of (ConicParameterOverlap a c)) ≅ pullback P₁ P₂ :=
  (olderGlobalConicOverlap_isPullback hπ data D j hj r hr hk0 hk).isoPullback

/-- The global overlap comparison preserves its first rational parameter projection. -/
@[reassoc] theorem olderGlobalConicOverlapIso_first :
    (olderGlobalConicOverlapIso hπ data D j hj r hr hk0 hk).hom ≫ pullback.fst P₁ P₂ = l :=
  (olderGlobalConicOverlap_isPullback hπ data D j hj r hr hk0 hk).isoPullback_hom_fst

/-- The global overlap comparison preserves its second rational parameter projection. -/
@[reassoc] theorem olderGlobalConicOverlapIso_second :
    (olderGlobalConicOverlapIso hπ data D j hj r hr hk0 hk).hom ≫ pullback.snd P₁ P₂ = r₀ :=
  (olderGlobalConicOverlap_isPullback hπ data D j hj r hr hk0 hk).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
