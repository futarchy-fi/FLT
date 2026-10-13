/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationFpqcOrbitComparison
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyOpen

/-!
# The full relation orbit topology for fppf covers

A flat surjection locally of finite presentation identifies its target with
the full relation orbit topology. No quasi-compactness of the source is required.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
universe u
namespace FLT.Mazur.RelativeRelationOrbit
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme.{u}} {A U T : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q) (g : U ⟶ T)
  (H : IsPullback p q g g)
  [Flat g.left] [LocallyOfFinitePresentation g.left] [Surjective g.left]

/-- The actual original quotient comparison is a quotient map for an fppf cover. -/
theorem fppfKernelQuotientComparison_isQuotientMap :
    IsQuotientMap (kernelQuotientComparison e g H).base := by
  apply (projection_isQuotientMap e).of_comp_isQuotientMap
  have he : (kernelQuotientComparison e g H).base ∘ projection e = g.left :=
    funext (kernelQuotientComparison_apply e g H)
  rw [he]
  exact g.left.isOpenMap.isQuotientMap g.left.continuous g.left.surjective

/-- The original invariant quotient and the actual fppf target have the same topology. -/
theorem fppfKernelQuotientComparison_base_isIso :
    IsIso (kernelQuotientComparison e g H).base :=
  TopCat.isIso_of_bijective_of_isOpenMap _
    ⟨kernelQuotientComparison_injective e g H,
      (fppfKernelQuotientComparison_isQuotientMap e g H).surjective⟩
    ((fppfKernelQuotientComparison_isQuotientMap e g H).isCoinducing.isOpenMap_of_injective
      (kernelQuotientComparison_injective e g H))

end FLT.Mazur.RelativeRelationOrbit
