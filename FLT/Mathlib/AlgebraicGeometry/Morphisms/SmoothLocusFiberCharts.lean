/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusOpenBase

/-!
# Fibre charts and their smooth loci

Open charts on the source induce open charts on the canonical fibre.
An open chart on the base induces an isomorphism of canonical fibres.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u
variable {X Y Z P U : Scheme.{u}}

/-- A canonical fibre of a locally finitely presented map is locally finitely presented. -/
instance Scheme.Hom.fiberToSpecResidueField_lfp (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] (y : Y) :
    LocallyOfFinitePresentation (f.fiberToSpecResidueField y) :=
  inferInstanceAs (LocallyOfFinitePresentation (pullback.snd _ _))

/-- The map between canonical fibres induced by a Cartesian square. -/
def Scheme.Hom.fiberMapOfIsPullback {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (y : Y) :
    b.fiber y ⟶ f.fiber (g y) :=
  pullback.map _ _ _ _ a (Spec.map (g.residueFieldMap y)) g h.w.symm (by simp)

/-- The induced square over the residue fields is Cartesian. -/
theorem Scheme.Hom.isPullback_fiberMapOfIsPullback {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (y : Y) :
    IsPullback (Scheme.Hom.fiberMapOfIsPullback h y) (b.fiberToSpecResidueField y)
      (f.fiberToSpecResidueField (g y)) (Spec.map (g.residueFieldMap y)) :=
  isPullback_fiberToSpecResidueField_of_isPullback h y

/-- Restricting the base to an open chart preserves the canonical fibre. -/
instance Scheme.Hom.fiberMapOfIsPullback_isIso {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (y : Y)
    [IsOpenImmersion g] : IsIso (Scheme.Hom.fiberMapOfIsPullback h y) :=
  (Scheme.Hom.isPullback_fiberMapOfIsPullback h y).isIso_fst_of_isIso

/-- The fibre comparison respects the maps to the original source. -/
@[reassoc (attr := simp)]
theorem Scheme.Hom.fiberMapOfIsPullback_fiberι {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g) (y : Y) :
    Scheme.Hom.fiberMapOfIsPullback h y ≫ f.fiberι (g y) = b.fiberι y ≫ a := by
  simp [Scheme.Hom.fiberMapOfIsPullback, Scheme.Hom.fiberι]

/-- The fibre isomorphism for an open base chart identifies the smooth loci. -/
theorem Scheme.Hom.preimage_smoothLocus_fiberMapOfIsPullback
    {a : P ⟶ X} {b : P ⟶ Y} {f : X ⟶ Z} {g : Y ⟶ Z}
    (h : IsPullback a b f g) (y : Y)
    [IsOpenImmersion g] [LocallyOfFinitePresentation f]
    [LocallyOfFinitePresentation b] :
    Scheme.Hom.fiberMapOfIsPullback h y ⁻¹ᵁ
      (f.fiberToSpecResidueField (g y)).smoothLocus =
        (b.fiberToSpecResidueField y).smoothLocus := by
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  rw! [(Scheme.Hom.isPullback_fiberMapOfIsPullback h y).w]
  exact Scheme.Hom.smoothLocus_comp_isIso _ _

/-- Restricting the source induces the usual map of canonical fibres. -/
def Scheme.Hom.fiberPrecomp (f : X ⟶ Y) (i : U ⟶ X) (y : Y) :
    (i ≫ f).fiber y ⟶ f.fiber y :=
  (pullbackRightPullbackFstIso f (Y.fromSpecResidueField y) i).inv ≫ pullback.snd _ _

/-- An open source chart induces an open chart on the fibre. -/
instance Scheme.Hom.fiberPrecomp_isOpenImmersion (f : X ⟶ Y) (i : U ⟶ X)
    (y : Y) [IsOpenImmersion i] : IsOpenImmersion (f.fiberPrecomp i y) := by
  dsimp [Scheme.Hom.fiberPrecomp]
  infer_instance

/-- The source-chart map respects the fibre inclusion. -/
@[reassoc (attr := simp)]
theorem Scheme.Hom.fiberPrecomp_fiberι (f : X ⟶ Y) (i : U ⟶ X) (y : Y) :
    f.fiberPrecomp i y ≫ f.fiberι y = (i ≫ f).fiberι y ≫ i := by
  simp [Scheme.Hom.fiberPrecomp, Scheme.Hom.fiberι]

/-- The source-chart map is a morphism over the residue field. -/
@[reassoc (attr := simp)]
theorem Scheme.Hom.fiberPrecomp_fiberToSpecResidueField
    (f : X ⟶ Y) (i : U ⟶ X) (y : Y) :
    f.fiberPrecomp i y ≫ f.fiberToSpecResidueField y =
      (i ≫ f).fiberToSpecResidueField y := by
  simp [Scheme.Hom.fiberPrecomp, Scheme.Hom.fiberToSpecResidueField]

/-- Smooth loci restrict along the induced source chart on a fibre. -/
theorem Scheme.Hom.preimage_smoothLocus_fiberPrecomp
    (f : X ⟶ Y) (i : U ⟶ X) (y : Y)
    [LocallyOfFinitePresentation f] [IsOpenImmersion i] :
    f.fiberPrecomp i y ⁻¹ᵁ (f.fiberToSpecResidueField y).smoothLocus =
      ((i ≫ f).fiberToSpecResidueField y).smoothLocus := by
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  congr 1
  exact Scheme.Hom.fiberPrecomp_fiberToSpecResidueField _ _ _

end AlgebraicGeometry
