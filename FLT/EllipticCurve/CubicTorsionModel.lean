/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.EllipticCurve.CubicGroupScheme
/-! # The represented kernel of multiplication on the cubic group scheme -/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open MonoidalCategory CartesianMonoidalCategory MonObj
set_option backward.isDefEq.respectTransparency false
@[expose] public noncomputable section
namespace WeierstrassCurve.CubicCharts
universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)
variable [IsNoetherianRing R] [_root_.IsReduced R] [W.IsElliptic]

/-- Multiplication by a natural number on the constructed group scheme. -/
def multiplicationOver (n : ℕ) : groupModel W ⟶ groupModel W := (𝟙 (groupModel W)) ^ n

theorem multiplicationOver_precomp {X : Over (Spec (.of R))}
    (f : X ⟶ groupModel W) (n : ℕ) :
    f ≫ multiplicationOver W n = f ^ n := by
  have h := map_pow (((yonedaGrpObj (groupModel W)).map f.op).hom)
    (𝟙 (groupModel W)) n
  change f ≫ (𝟙 (groupModel W)) ^ n = (f ≫ 𝟙 (groupModel W)) ^ n at h
  simpa only [multiplicationOver, Category.comp_id] using h

theorem one_precomp {X : Over (Spec (.of R))} (f : X ⟶ groupModel W) :
    f ≫ (1 : groupModel W ⟶ groupModel W) = 1 :=
  map_one (((yonedaGrpObj (groupModel W)).map f.op).hom)

/-- The represented kernel of multiplication by n on the actual cubic group scheme. -/
def torsionModel (n : ℕ) : Over (Spec (.of R)) :=
  equalizer (multiplicationOver W n) (1 : groupModel W ⟶ groupModel W)

/-- Its maps from every base scheme are precisely the points killed by n. -/
def torsionModelPointEquiv (n : ℕ) (X : Over (Spec (.of R))) :
    (X ⟶ torsionModel W n) ≃ {f : X ⟶ groupModel W // f ^ n = 1} where
  toFun f := ⟨f ≫ equalizer.ι (multiplicationOver W n) 1, by
    rw [← multiplicationOver_precomp, Category.assoc, equalizer.condition,
      ← Category.assoc, one_precomp]⟩
  invFun f := equalizer.lift f.1 (by
    rw [multiplicationOver_precomp, one_precomp, f.2])
  left_inv f := by
    apply equalizer.hom_ext
    simp
  right_inv f := by
    apply Subtype.ext
    simp

end WeierstrassCurve.CubicCharts
