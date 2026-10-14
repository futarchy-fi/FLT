/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Flat

/-!
# The actual quotient map on smooth loci under field extension

A faithfully flat quasi-compact field base change restricts to a quotient
map on the full relative smooth opens, preserving their original inclusions.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.SmoothLocusDescent
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {K L : Type u} [Field K] [Field L] {X Y : Scheme.{u}}
  {f : X ⟶ Spec (.of K)} {g : Y ⟶ Spec (.of L)}
  {p : Y ⟶ X} {q : Spec (.of L) ⟶ Spec (.of K)}
  (H : IsPullback p g f q)
  [LocallyOfFinitePresentation f] [LocallyOfFinitePresentation g]

/-- The original projection on the entire relative smooth locus. -/
def map : g.smoothLocus.toScheme ⟶ f.smoothLocus.toScheme :=
  p.resLE f.smoothLocus g.smoothLocus
    (Scheme.Hom.preimage_smoothLocus_fieldExtension_of_isPullback H).symm.le

/-- Restriction keeps the original whole-model projection. -/
@[reassoc] theorem map_inclusion : map H ≫ f.smoothLocus.ι = g.smoothLocus.ι ≫ p :=
  Scheme.Hom.resLE_comp_ι _ _

/-- The entire smooth-open restriction is cartesian inside the original models. -/
theorem map_isPullback : IsPullback (map H) g.smoothLocus.ι f.smoothLocus.ι p := by
  apply IsOpenImmersion.isPullback
  · exact (map_inclusion H).symm
  · simpa only [Scheme.Opens.opensRange_ι] using
      Scheme.Hom.preimage_smoothLocus_fieldExtension_of_isPullback H

/-- The restricted original projection remains a quotient map. -/
theorem map_isQuotientMap [Flat q] [Surjective q] [QuasiCompact q] :
    Topology.IsQuotientMap (map H) := by
  let _ : Flat p := MorphismProperty.of_isPullback H.flip inferInstance
  let _ : Surjective p := MorphismProperty.of_isPullback H.flip inferInstance
  let _ : QuasiCompact p := MorphismProperty.of_isPullback H.flip inferInstance
  let _ : Flat (map H) := MorphismProperty.of_isPullback (map_isPullback H).flip
    inferInstance
  let _ : Surjective (map H) := MorphismProperty.of_isPullback (map_isPullback H).flip
    inferInstance
  let _ : QuasiCompact (map H) := MorphismProperty.of_isPullback (map_isPullback H).flip
    inferInstance
  exact Flat.isQuotientMap_of_surjective (map H)

end FLT.Mazur.SmoothLocusDescent
