/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothInversion

/-!
# Product charts on the entire original smooth polygon

Pairs of original identity charts cover the relative product. The cover
uses the actual product of the original identity group as each domain.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj GrpObj
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
  completePointWeierstrassCurve completePointToIntegralCubic completeRotation
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "M" => completeOriginalSmoothOver K n h
local notation "C" => completeIdentityChartCover K n h (0 : Fin n)

/-- The raw pullback cover supplied by the two original smooth atlases. -/
def completeSmoothProductRawCover : ((M) ⊗ (M)).left.OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (C) (C) (M).hom (M).hom

/-- Each raw product chart is the actual relative product of the identity group. -/
def completeSmoothProductChartIso (b c : ZMod n) :
    (completeSmoothProductRawCover K n h).X (b, c) ≅ ((G).X ⊗ (G).X).left :=
  pullback.congrHom (completeIdentityChart K n h 0 b).w
    (completeIdentityChart K n h 0 c).w

/-- The product chart comparison preserves the actual pair of chart embeddings. -/
theorem completeSmoothProductChartIso_map (b c : ZMod n) :
    (completeSmoothProductChartIso K n h b c).inv ≫
        (completeSmoothProductRawCover K n h).f (b, c) =
      (completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c).left := by
  simp only [completeSmoothProductRawCover, Scheme.Pullback.openCoverOfLeftRight_f,
    completeSmoothProductChartIso, completeIdentityChartCover, pullback.congrHom_inv,
    Over.tensorHom_left]
  apply pullback.hom_ext <;>
    simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]

/-- All pairs of original identity-group charts cover the full relative smooth product. -/
def completeSmoothProductCover : ((M) ⊗ (M)).left.OpenCover :=
  (completeSmoothProductRawCover K n h).copy (ZMod n × ZMod n)
    (fun _ ↦ ((G).X ⊗ (G).X).left)
    (fun p ↦ (completeIdentityChart K n h 0 p.1 ⊗ₘ
      completeIdentityChart K n h 0 p.2).left) (Equiv.refl _)
    (fun p ↦ (completeSmoothProductChartIso K n h p.1 p.2).symm)
    (fun p ↦ (completeSmoothProductChartIso_map K n h p.1 p.2).symm)

/-- Morphisms from the full smooth product are determined by all pairs of charts. -/
theorem completeSmoothProduct_hom_ext {Y : Over (Spec (.of (PowerSeries K)))}
    (f g : (M) ⊗ (M) ⟶ Y)
    (he : ∀ b c : ZMod n,
      (completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c) ≫ f =
      (completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c) ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply (completeSmoothProductCover K n h).hom_ext
  rintro ⟨b, c⟩
  exact congrArg Over.Hom.left (he b c)

end FLT.Mazur.PolygonInfinitesimalStages
