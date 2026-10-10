/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeDescentPairTransport

/-!
# Original transport on an arbitrary overlap test

The fiber-product universal property identifies the normalized original
overlap with transport between the two maps of any test chart.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SchemeGeometricDescent.Data
open SchemeOverlapDiagonalChart
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y T : Scheme.{u}} {p : Y ⟶ X} {M : Y.Modules} (D : Data p M)

/-- Every overlap test recovers transport between its two original source maps. -/
lemma normalize_overlap_eq_transport (t : T ⟶ Limits.pullback p p) (b c : T ⟶ Y)
    (hb : t ≫ Limits.pullback.fst p p = b) (hc : t ≫ Limits.pullback.snd p p = c)
    (w : b ≫ p = c ≫ p) :
    normalize (Limits.pullback.fst p p) (Limits.pullback.snd p p) t b c hb hc M D.overlap =
      D.transport b c w := by
  have ht : Limits.pullback.lift b c w = t := by
    apply Limits.pullback.hom_ext
    · simpa only [Limits.pullback.lift_fst] using hb.symm
    · simpa only [Limits.pullback.lift_snd] using hc.symm
  unfold transport
  subst t
  rfl

end FLT.Mazur.SchemeGeometricDescent.Data
