/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mathlib.AlgebraicGeometry.Morphisms.SmoothLocusTransport
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Smooth loci and open changes of base

The smooth locus is unchanged by restricting the target to an open subscheme.
The pullback formula is useful when checking fibre criteria on affine charts.
-/

public noncomputable section
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits

namespace AlgebraicGeometry

universe u
variable {X Y Z P : Scheme.{u}}

/-- Postcomposing with an open immersion does not change the smooth locus. -/
theorem Scheme.Hom.smoothLocus_comp_isOpenImmersion (f : X ⟶ Y) (g : Y ⟶ Z)
    [LocallyOfFinitePresentation f] [IsOpenImmersion g] :
    (f ≫ g).smoothLocus = f.smoothLocus := by
  ext x
  change (Scheme.Hom.stalkMap (f ≫ g) x).hom.FormallySmooth ↔ _
  rw [Scheme.Hom.stalkMap_comp, CommRingCat.hom_comp,
    RingHom.FormallySmooth.respectsIso.cancel_left_isIso]
  rfl

/-- Smooth loci commute with a pullback along an open immersion of the base. -/
theorem Scheme.Hom.preimage_smoothLocus_openBase {a : P ⟶ X} {b : P ⟶ Y}
    {f : X ⟶ Z} {g : Y ⟶ Z} (h : IsPullback a b f g)
    [LocallyOfFinitePresentation f] [IsOpenImmersion g] :
    let : LocallyOfFinitePresentation b := MorphismProperty.of_isPullback h inferInstance
    a ⁻¹ᵁ f.smoothLocus = b.smoothLocus := by
  let : LocallyOfFinitePresentation b := MorphismProperty.of_isPullback h inferInstance
  have : IsOpenImmersion a := MorphismProperty.of_isPullback h.flip inferInstance
  rw [Scheme.Hom.preimage_smoothLocus_eq]
  rw! [h.w]
  exact b.smoothLocus_comp_isOpenImmersion g

end AlgebraicGeometry
