/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarImageKernelNeighborhood
public import Mathlib.AlgebraicGeometry.Sites.Fpqc

/-!
# Coverage of original image neighborhoods

The exact scalar image projection has dense range for an affine source.
This remains true on every image open. Closedness of the restricted image,
in particular local integral geometry, therefore supplies actual coverage.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarImageQuotient
open SchemeScalarPrincipalNeighborhood FlatScalarFunctionPushout
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] {X : Scheme.{0}} [IsAffine X]
  (f : X ⟶ Spec (.of R))

/-- Exact image equations imply topological density of the full source image. -/
theorem projection_denseRange : DenseRange (projection f) := by
  rw [denseRange_iff_closure_range, projection, scalarMorphism_range_eq_comap,
    PrimeSpectrum.closure_range_comap,
    (RingHom.injective_iff_ker_eq_bot _).mp (RingHom.kerLift_injective _)]
  exact PrimeSpectrum.zeroLocus_bot

variable (U : (Spec (.of (Scalars f))).Opens)

/-- Every original image neighborhood retains the dense full source image. -/
theorem projection_restrict_denseRange : DenseRange ((projection f) ∣_ U) := by
  rw [denseRange_iff_closure_range, morphismRestrict_base, Set.range_restrictPreimage,
    ← U.2.isOpenEmbedding_subtypeVal.isOpenMap.preimage_closure_eq_closure_preimage
      continuous_subtype_val,
    (projection_denseRange f).closure_range]
  exact Set.preimage_univ

/-- Closed range on one original neighborhood makes its full image projection surjective. -/
theorem projection_restrict_surjective_of_closed
    (hc : IsClosed (Set.range ((projection f) ∣_ U))) :
    Surjective ((projection f) ∣_ U) := by
  constructor
  apply Set.range_eq_univ.mp
  rw [← hc.closure_eq]
  exact (projection_restrict_denseRange f U).closure_range

/-- Local integral geometry supplies full original image coverage without global integrality. -/
theorem projection_restrict_surjective_of_integral
    [IsIntegralHom ((projection f) ∣_ U)] : Surjective ((projection f) ∣_ U) :=
  projection_restrict_surjective_of_closed f U ((projection f) ∣_ U).isClosedMap.isClosed_range

/-- Flat integral geometry on an original open constructs effective descent onto that open. -/
theorem projection_restrict_effectiveEpi_of_flat_integral
    [Flat ((projection f) ∣_ U)] [IsIntegralHom ((projection f) ∣_ U)] :
    EffectiveEpi ((projection f) ∣_ U) := by
  let _ := projection_restrict_surjective_of_integral f U
  infer_instance

end FLT.Mazur.SchemeScalarImageQuotient
