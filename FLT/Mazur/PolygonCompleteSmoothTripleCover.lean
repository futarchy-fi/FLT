/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteSmoothMultiplication

/-!
# Triple charts on the entire original smooth polygon

Triples of original identity charts cover the relative triple product. The cover
uses the actual triple product of the original identity group as each domain.
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

/-- The raw cover of the triple relative product by pairs and single charts. -/
def completeSmoothTripleRawCover : (((M) ⊗ (M)) ⊗ (M)).left.OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight (completeSmoothProductCover K n h) (C)
    ((M) ⊗ (M)).hom (M).hom

/-- Each raw triple chart is the actual relative triple product of the identity group. -/
def completeSmoothTripleChartIso (b c d : ZMod n) :
    (completeSmoothTripleRawCover K n h).X ((b, c), d) ≅ (((G).X ⊗ (G).X) ⊗ (G).X).left :=
  pullback.congrHom (completeIdentityChart K n h 0 b ⊗ₘ
    completeIdentityChart K n h 0 c).w (completeIdentityChart K n h 0 d).w

/-- The triple chart comparison preserves the actual triple of chart embeddings. -/
theorem completeSmoothTripleChartIso_map (b c d : ZMod n) :
    (completeSmoothTripleChartIso K n h b c d).inv ≫
        (completeSmoothTripleRawCover K n h).f ((b, c), d) =
      ((completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c) ⊗ₘ
        completeIdentityChart K n h 0 d).left := by
  simp only [completeSmoothTripleRawCover, Scheme.Pullback.openCoverOfLeftRight_f,
    completeSmoothTripleChartIso, completeIdentityChartCover, completeSmoothProductCover,
    Scheme.Cover.copy_f,
    pullback.congrHom_inv,
    Over.tensorHom_left]
  apply pullback.hom_ext <;>
    simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc, Category.comp_id]

/-- All triples of original identity-group charts cover the full relative smooth triple product. -/
def completeSmoothTripleCover : (((M) ⊗ (M)) ⊗ (M)).left.OpenCover :=
  (completeSmoothTripleRawCover K n h).copy ((ZMod n × ZMod n) × ZMod n)
    (fun _ ↦ (((G).X ⊗ (G).X) ⊗ (G).X).left)
    (fun p ↦ ((completeIdentityChart K n h 0 p.1.1 ⊗ₘ
      completeIdentityChart K n h 0 p.1.2) ⊗ₘ completeIdentityChart K n h 0 p.2).left)
    (Equiv.refl _)
    (fun p ↦ (completeSmoothTripleChartIso K n h p.1.1 p.1.2 p.2).symm)
    (fun p ↦ (completeSmoothTripleChartIso_map K n h p.1.1 p.1.2 p.2).symm)

/-- Morphisms from the full smooth triple product are determined by all triples of charts. -/
theorem completeSmoothTriple_hom_ext {Y : Over (Spec (.of (PowerSeries K)))}
    (f g : ((M) ⊗ (M)) ⊗ (M) ⟶ Y)
    (he : ∀ b c d : ZMod n,
      ((completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c) ⊗ₘ
        completeIdentityChart K n h 0 d) ≫ f =
      ((completeIdentityChart K n h 0 b ⊗ₘ completeIdentityChart K n h 0 c) ⊗ₘ
        completeIdentityChart K n h 0 d) ≫ g) : f = g := by
  apply Over.OverMorphism.ext
  apply (completeSmoothTripleCover K n h).hom_ext
  rintro ⟨⟨b, c⟩, d⟩
  exact congrArg Over.Hom.left (he b c d)

end FLT.Mazur.PolygonInfinitesimalStages
