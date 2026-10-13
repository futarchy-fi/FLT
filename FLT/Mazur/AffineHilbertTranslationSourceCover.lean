/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertTranslationSource

/-!
# Covering source refinements with genuinely varying translations

A cover of the original translation scheme induces a cover of the ORIGINAL
parameter source. Each member maps to the corresponding changed Hilbert
chart, with the original Picard section preserved. These are source covers;
full-envelope effectiveness is not inferred from their covering property.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  {ι : Type} (W : ι → Over (Spec (.of R))) (b : ∀ i, W i ⟶ V)
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)

/-- Every original source point survives some genuine translation refinement. -/
theorem translationSources_jointly_surjective
    (hb : ∀ v : V.left, ∃ i, ∃ w : (W i).left, (b i).left w = v) (x : A.left) :
    ∃ i, ∃ y : (translationSource f d (b i) k).left,
      (translationSourceMap f d (b i) k).left y = x := by
  obtain ⟨i, w, hw⟩ := hb ((k ≫ variableHilbertBase f d V).left x)
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
    ((translationSource_isPullback f d (b i) k).map (Over.forget _)) x w hw.symm
  exact ⟨i, y, hy⟩

/-- The constructed source arrows form a cover for any base-change-stable property. -/
def translationSourceCover (P : MorphismProperty Scheme) [P.IsStableUnderBaseChange]
    (hb : ∀ v : V.left, ∃ i, ∃ w : (W i).left, (b i).left w = v)
    (hP : ∀ i, P (b i).left) : Scheme.Cover (Scheme.precoverage P) A.left where
  I₀ := ι
  X i := (translationSource f d (b i) k).left
  f i := (translationSourceMap f d (b i) k).left
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    exact ⟨translationSources_jointly_surjective f d V W b k hb,
      fun i ↦ translationSourceMap_property f d (b i) k P (hP i)⟩

variable (C : V.left.OpenCover)

/-- Actual varying translation opens give an open cover of the original parameter source. -/
def translationSourceOpenCover : A.left.OpenCover :=
  translationSourceCover f d V (fun i ↦ Over.mk (C.f i ≫ V.hom))
    (fun i ↦ Over.homMk (C.f i)) k (@IsOpenImmersion) (fun x ↦ C.exists_eq x)
    (fun i ↦ (show IsOpenImmersion (C.f i) from inferInstance))

/-- With affine translations and source, the constructed open cover has affine members. -/
theorem translationSourceOpenCover_affine [IsAffine A.left] [IsAffine V.left]
    [∀ i, IsAffine (C.X i)] (i : C.I₀) :
    IsAffine ((translationSourceOpenCover f d V k C).X i) := by
  let b : Over.mk (C.f i ≫ V.hom) ⟶ V := Over.homMk (C.f i)
  change IsAffine (translationSource f d b k).left
  let _ : IsAffine (Over.mk (C.f i ≫ V.hom)).left :=
    inferInstanceAs (IsAffine (C.X i))
  exact translationSource_affine f d b k

/-- The canonical affine translation cover supplies genuine affine source refinements. -/
def translationAffineSourceCover : A.left.OpenCover :=
  translationSourceOpenCover f d V k V.left.affineCover

instance translationAffineSourceCover_affine [IsAffine A.left] [IsAffine V.left]
    (i : (translationAffineSourceCover f d V k).I₀) :
    IsAffine ((translationAffineSourceCover f d V k).X i) :=
  translationSourceOpenCover_affine f d V k V.left.affineCover i

end FLT.Mazur.HilbertChart.AffineRestriction
