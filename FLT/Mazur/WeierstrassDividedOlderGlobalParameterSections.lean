/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOlderGlobalComponentSections
public import FLT.Mazur.WeierstrassModificationXConicParameterSections

/-!
# Ordered parameter origins in the retained global fiber

Both rational parameter origins give the corresponding older global section.
The original tangent order is retained without a nonzero hypothesis on c.
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
  (D : SplitNodeDepth W π depth) (j : ℕ) (hj : j + 1 ≤ n)
  (r : ℕ) (hr : j + 1 + r ≤ n)
  (hk0 : 0 < start + j) (hk : 2 * (start + j + 1) ≤ depth)
open WeierstrassModificationX
local notation "d" => data (Fin.mk (j + 1) (Nat.lt_succ_of_le hj))
local notation "c" => residue R (Data.b6 d)

/-- The first parameter origin is the first ordered global incidence section. -/
@[reassoc] theorem olderGlobalFirstSection_parameter :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      olderGlobalMiddleConicFirstParameter hπ data D j hj r hr hk0 hk =
        olderGlobalFirstSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalMiddleConicFirstParameter,
    conicFirstParameterIso_origin_assoc, olderGlobalFirstSection_conic]

/-- The second parameter origin is the opposite ordered global incidence section. -/
@[reassoc] theorem olderGlobalSecondSection_parameter :
    Spec.map (CommRingCat.ofHom (conicParameterOrigin c).toRingHom) ≫
      olderGlobalMiddleConicSecondParameter hπ data D j hj r hr hk0 hk =
        olderGlobalSecondSection hπ data D j hj r hr hk0 hk := by
  rw [olderGlobalMiddleConicSecondParameter,
    conicSecondParameterIso_origin_assoc, olderGlobalSecondSection_conic]

end FLT.Mazur.WeierstrassDividedDepth
