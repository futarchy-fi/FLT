/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonInfinitesimalMarkingRegular
public import FLT.Mazur.AffineImmersionSectionCoordinates

/-!
# The original marking equation on its full chart image

Transport the specified arithmetic equation to the actual image open in the
glued family. This supplies a whole affine Cartier chart for pole numerators.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimal
open PolygonSmoothing AffineImmersionSectionCoordinates
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable (R : Type u) [CommRing R] (t : R) [Fact (IsNilpotent t)]
  (n : ℕ) (h : 2 ≤ n) (i j : Fin n) (a : Rˣ)

/-- The specified equation on the actual image of the original whole arithmetic chart. -/
def markingImageEquation : Γ(scheme R t n h, (imageAffine (chart R t n h j)).1) :=
  (coordinates (chart R t n h j)).symm (chartMarkingEquation R t n i j a)

/-- Original arithmetic coordinates recover precisely the same marking equation. -/
theorem markingImageEquation_coordinate :
    coordinates (chart R t n h j) (markingImageEquation R t n h i j a) =
      chartMarkingEquation R t n i j a :=
  (coordinates (chart R t n h j)).apply_symm_apply _

/-- The image-open equation remains regular, retaining every coefficient nilpotent. -/
theorem markingImageEquation_regular : IsRegular (markingImageEquation R t n h i j a) := by
  have hr := chartMarkingEquation_regular R t n h i j a
  constructor
  · intro b c hb
    apply (coordinates (chart R t n h j)).injective
    apply hr.left
    simpa only [map_mul, markingImageEquation, RingEquiv.apply_symm_apply] using
      congrArg (coordinates (chart R t n h j)) hb
  · intro b c hb
    apply (coordinates (chart R t n h j)).injective
    apply hr.right
    simpa only [map_mul, markingImageEquation, RingEquiv.apply_symm_apply] using
      congrArg (coordinates (chart R t n h j)) hb

/-- The full original global ideal on the image has the specified principal equation. -/
theorem markingImageIdeal_equation :
    (marking R t n h i a).ker.ideal (imageAffine (chart R t n h j)) =
      Ideal.span {markingImageEquation R t n h i j a} := by
  rw [ideal_comap]
  let e := (Scheme.ΓSpecIso (.of (ChartRing t))).commRingCatIsoToRingEquiv
  have he : Ideal.map e.toRingHom
      (((marking R t n h i a).ker.comap (chart R t n h j)).ideal
        ⟨⊤, isAffineOpen_top (Spec (.of (ChartRing t)))⟩) =
      Ideal.span {chartMarkingEquation R t n i j a} :=
    (Ideal.map_comap_of_equiv e).trans (marking_ideal_chart_coordinate R t n h i j a)
  change Ideal.comap (coordinates (chart R t n h j)).toRingHom
    (Ideal.map e.toRingHom _) = _
  rw [he]
  change Ideal.comap (coordinates (chart R t n h j)) _ = _
  rw [← Ideal.map_symm (coordinates (chart R t n h j)),
    Ideal.map_span, Set.image_singleton]
  rfl

/-- Every original ideal power keeps this same equation to its exact degree. -/
theorem markingImageIdeal_power_equation (d : ℕ) :
    ((marking R t n h i a).ker ^ d).ideal (imageAffine (chart R t n h j)) =
      Ideal.span {markingImageEquation R t n h i j a ^ d} := by
  change (marking R t n h i a).ker.ideal (imageAffine (chart R t n h j)) ^ d = _
  rw [markingImageIdeal_equation, Ideal.span_singleton_pow]

end FLT.Mazur.PolygonInfinitesimal
