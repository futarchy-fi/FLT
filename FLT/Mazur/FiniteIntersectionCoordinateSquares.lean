/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteIntersectionSectionDiagram

/-!
# Open immersions and cartesian squares in intersection coordinates

The natural spectrum identifications transport the actual open immersion
and union-pullback laws to the coordinate algebra diagram. These are the
geometric hypotheses needed by finite affine atlas diagram descent.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {ι : Type v}
  (U : ι → X.Opens) (p : X ⟶ Spec (.of A)) [X.IsSeparated]
  (hU : ∀ i, IsAffineOpen (U i))

include hU

/-- The spectrum of every coordinate restriction map is an open immersion. -/
theorem finiteIntersectionSectionDiagram_map_isOpenImmersion
    {s t : NonemptyChartSet ι} (f : s ⟶ t) :
    IsOpenImmersion (Spec.map (CommRingCat.ofHom
      (((finiteIntersectionSectionDiagram U p).map f).hom.toRingHom))) := by
  have he : Spec.map (CommRingCat.ofHom
      (((finiteIntersectionSectionDiagram U p).map f).hom.toRingHom)) =
      (finiteIntersectionSectionSpecIso U p hU t).inv ≫
        (finiteIntersectionSchemeDiagram U).map f.op ≫
          (finiteIntersectionSectionSpecIso U p hU s).hom := by
    apply (cancel_epi (finiteIntersectionSectionSpecIso U p hU t).hom).mp
    simpa using finiteIntersectionSectionSpecIso_naturality U p hU f
  rw [he]
  infer_instance

/-- A marked union square is cartesian in the section-algebra spectrum diagram. -/
theorem finiteIntersectionSectionDiagram_isPullback (r s t : NonemptyChartSet ι)
    (hrs : r ≤ s) (hrt : r ≤ t) :
    IsPullback
      (Spec.map (CommRingCat.ofHom (((finiteIntersectionSectionDiagram U p).map
        (homOfLE (le_unionChartSet_left s t))).hom.toRingHom)))
      (Spec.map (CommRingCat.ofHom (((finiteIntersectionSectionDiagram U p).map
        (homOfLE (le_unionChartSet_right s t))).hom.toRingHom)))
      (Spec.map (CommRingCat.ofHom (((finiteIntersectionSectionDiagram U p).map
        (homOfLE hrs)).hom.toRingHom)))
      (Spec.map (CommRingCat.ofHom (((finiteIntersectionSectionDiagram U p).map
        (homOfLE hrt)).hom.toRingHom))) := by
  apply (finiteIntersectionOpen_isPullback U r s t hrs hrt).of_iso
    (finiteIntersectionSectionSpecIso U p hU (unionChartSet s t))
    (finiteIntersectionSectionSpecIso U p hU s)
    (finiteIntersectionSectionSpecIso U p hU t)
    (finiteIntersectionSectionSpecIso U p hU r)
  · exact (finiteIntersectionSectionSpecIso_naturality U p hU _).symm
  · exact (finiteIntersectionSectionSpecIso_naturality U p hU _).symm
  · exact (finiteIntersectionSectionSpecIso_naturality U p hU _).symm
  · exact (finiteIntersectionSectionSpecIso_naturality U p hU _).symm

end FLT.Mazur.Approximation
