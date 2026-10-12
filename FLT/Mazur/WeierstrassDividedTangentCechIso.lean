/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedTangentCech

/-!
# The actual finite-model overlap isomorphism

Both copies of the tangent-cover finite model over the genuine coefficient
Cech scheme identify with the same base change of the integral finite model.
Their comparison is constructed and preserves the exact original projection.
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
  (j : ℕ) (hj : j ≤ n)
local notation "q" => nodeTangentCover W
local notation "p₁" => pullback.fst q q
local notation "p₂" => pullback.snd q q
local notation "base" => finiteGlobalStructure hπ data j hj
local notation "zs" => pullback.fst (p₁ ≫ q) base
local notation "zx" => pullback.snd (p₁ ≫ q) base
local notation "ys" => pullback.fst q base
local notation "yx" => pullback.snd q base
local notation "f₁" => finiteGlobalTangentCechFirst hπ data j hj
local notation "f₂" => finiteGlobalTangentCechSecond hπ data j hj

/-- The first actual overlap map is cartesian over the first coefficient projection. -/
theorem finiteGlobalTangentCechFirst_isPullback : IsPullback zs f₁ p₁ ys := by
  apply IsPullback.of_bot (v₂₁ := yx) (v₂₂ := q) (h₃₁ := base) _
    (finiteGlobalTangentCechFirst_structure hπ data j hj).symm
    (IsPullback.of_hasPullback q base)
  rw [finiteGlobalTangentCechFirst_projection]
  exact IsPullback.of_hasPullback _ _

/-- The second map is cartesian over the other original coefficient projection. -/
theorem finiteGlobalTangentCechSecond_isPullback : IsPullback zs f₂ p₂ ys := by
  apply IsPullback.of_bot (v₂₁ := yx) (v₂₂ := q) (h₃₁ := base) _
    (finiteGlobalTangentCechSecond_structure hπ data j hj).symm
    (IsPullback.of_hasPullback q base)
  rw [finiteGlobalTangentCechSecond_projection, ← pullback.condition (f := q) (g := q)]
  exact IsPullback.of_hasPullback _ _

/-- The constructed comparison of the two original finite-model pullbacks over the overlap. -/
def finiteGlobalTangentCechIso : pullback p₁ ys ≅ pullback p₂ ys :=
  (finiteGlobalTangentCechFirst_isPullback hπ data j hj).isoPullback.symm ≪≫
    (finiteGlobalTangentCechSecond_isPullback hπ data j hj).isoPullback

/-- The comparison is over the original coefficient Cech scheme. -/
@[reassoc] theorem finiteGlobalTangentCechIso_structure :
    (finiteGlobalTangentCechIso hπ data j hj).hom ≫ pullback.fst p₂ ys =
      pullback.fst p₁ ys := by
  simp only [finiteGlobalTangentCechIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, IsPullback.isoPullback_hom_fst, IsPullback.isoPullback_inv_fst]

/-- The comparison keeps the original integral finite-model projection on every chart. -/
@[reassoc] theorem finiteGlobalTangentCechIso_projection :
    (finiteGlobalTangentCechIso hπ data j hj).hom ≫ pullback.snd p₂ ys ≫ yx =
      pullback.snd p₁ ys ≫ yx := by
  simp only [finiteGlobalTangentCechIso, Iso.trans_hom, Iso.symm_hom,
    Category.assoc, IsPullback.isoPullback_hom_snd_assoc]
  rw [finiteGlobalTangentCechSecond_projection,
    ← finiteGlobalTangentCechFirst_projection hπ data j hj,
    IsPullback.isoPullback_inv_snd_assoc]

/-- The comparison intertwines the two actual model maps out of the common integral base change. -/
@[reassoc] theorem finiteGlobalTangentCechIso_comparison :
    (finiteGlobalTangentCechFirst_isPullback hπ data j hj).isoPullback.hom ≫
      (finiteGlobalTangentCechIso hπ data j hj).hom =
        (finiteGlobalTangentCechSecond_isPullback hπ data j hj).isoPullback.hom := by
  simp only [finiteGlobalTangentCechIso, Iso.trans_hom, Iso.symm_hom, Iso.hom_inv_id_assoc]

end FLT.Mazur.WeierstrassDividedDepth
