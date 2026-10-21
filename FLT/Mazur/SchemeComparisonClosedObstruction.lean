/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeComparisonCoverageLocus
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyClosed

/-!
# Closed obstructions for open full comparisons

An open comparison and a universally closed kernel-pair image map make
the entire missed image closed. Fiber coverage then constructs an original
neighborhood where the full comparison is surjective.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeComparisonCoverageLocus
variable {D K Z : Scheme.{0}} (k : D ⟶ K) (m : K ⟶ Z)
  [IsOpenImmersion k] [UniversallyClosed m]

/-- The image of all points missed by an open comparison is closed under a closed image map. -/
theorem missedImage_isClosed : IsClosed (m '' (Set.range k)ᶜ) :=
  m.isClosedMap _ k.isOpenEmbedding.isOpen_range.isClosed_compl

/-- The obstruction has no extra specialization points under closed image geometry. -/
theorem badImage_eq_missedImage : badImage k m = m '' (Set.range k)ᶜ :=
  (missedImage_isClosed k m).closure_eq

/-- Full coverage of one original fiber is equivalent to membership in the constructed open. -/
theorem mem_goodOpen_iff_fiber_coverage (z : Z) :
    z ∈ goodOpen k m ↔ ∀ w : K, m w = z → w ∈ Set.range k :=
  mem_goodOpen_iff_of_isClosed k m (missedImage_isClosed k m) z

/-- Closed geometry enlarges fiber coverage to an actual original image neighborhood. -/
theorem exists_neighborhood_of_closed_fiber_coverage (z : Z)
    (hz : ∀ w : K, m w = z → w ∈ Set.range k) :
    ∃ U : Z.Opens, z ∈ U ∧ Surjective (k ∣_ (m ⁻¹ᵁ U)) :=
  exists_neighborhood_of_fiber_coverage k m (missedImage_isClosed k m) z hz

end FLT.Mazur.SchemeComparisonCoverageLocus
