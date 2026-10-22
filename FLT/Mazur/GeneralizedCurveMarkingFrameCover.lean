/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveMarkingAffineDiagram
public import Mathlib.AlgebraicGeometry.Cover.Directed

/-!
# The actual directed cover by original affine marking frames

The affine frame existence theorem makes these chart bases a topological
basis. Their cover and its pullback to the original whole curve can therefore
be used to glue the actual local cubic morphisms.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group)

/-- Every original base point belongs to an actual framed affine marking chart. -/
def smoothMarkingFrameCover : S.OpenCover where
  I₀ := SmoothMarkingAffineChart E s
  X i := i.base.1.toScheme
  f i := i.base.1.ι
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, inferInstance⟩
    obtain ⟨i, hi, _⟩ := exists_smoothMarkingAffineChart E s
      (show x ∈ (⊤ : S.Opens) from trivial)
    exact ⟨i, ⟨x, hi⟩, rfl⟩

instance smoothMarkingFrameCoverPreorder : Preorder (smoothMarkingFrameCover E s).I₀ :=
  inferInstanceAs (Preorder (SmoothMarkingAffineChart E s))

/-- The original framed affine opens form a basis, including over nonseparated bases. -/
theorem smoothMarkingFrameCover_isBasis :
    TopologicalSpace.Opens.IsBasis
      (Set.range (fun i ↦ ((smoothMarkingFrameCover E s).f i).opensRange)) := by
  apply TopologicalSpace.Opens.isBasis_iff_nbhd.mpr
  intro V x hx
  obtain ⟨i, hi, hle⟩ := exists_smoothMarkingAffineChart E s hx
  refine ⟨i.base.1, ?_, hi, hle⟩
  exact ⟨i, Scheme.Opens.opensRange_ι _⟩

/-- Base-open inclusions make the actual frame cover locally directed. -/
instance smoothMarkingFrameCoverLocallyDirected :
    (smoothMarkingFrameCover E s).LocallyDirected :=
  .ofIsBasisOpensRange (by intros; simp only [smoothMarkingFrameCover,
    Scheme.Opens.opensRange_ι]; rfl) (smoothMarkingFrameCover_isBasis E s)

/-- The constructed cover transition is the original inclusion of affine opens. -/
theorem smoothMarkingFrameCover_trans {i j : SmoothMarkingAffineChart E s} (f : i ⟶ j) :
    (smoothMarkingFrameCover E s).trans f = S.homOfLE f.le := rfl

/-- On the whole curve the cover transition is the actual family restriction map. -/
theorem smoothMarkingFrameCover_curveTrans {i j : SmoothMarkingAffineChart E s}
    (f : i ⟶ j) :
    Scheme.Cover.trans ((smoothMarkingFrameCover E s).pullback₁ E.curve.hom) f =
      openRestrictionCurveMap E j.base.1 i.base.1 f.le := by
  apply (cancel_mono (Limits.pullback.fst E.curve.hom j.base.1.ι)).mp
  change Scheme.Cover.trans ((smoothMarkingFrameCover E s).pullback₁ E.curve.hom) f ≫
    ((smoothMarkingFrameCover E s).pullback₁ E.curve.hom).f j = _
  rw [Scheme.Cover.trans_map, openRestrictionCurveMap_fst]
  rfl

end FLT.Mazur.GeneralizedEllipticCurve
