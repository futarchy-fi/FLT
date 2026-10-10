/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProjectiveAmbientHilbertParameter
public import FLT.Mazur.ProperAmpleConverse

/-!
# Full finite-family classification from a proper ample ambient

The existing proper-ampleness theorem constructs a closed projective
presentation. Homogeneous avoidance then proves the full-fiber support
condition for the atlas of all affine opens, without an embedding input.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover FLT.Mazur.FCurve

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {Z : Scheme} (z : Z ⟶ Spec (.of R)) [IsProper z]
variable {L : Z.Modules} (hL : AmpleLineBundle L)
variable (d : ℕ) {X : Scheme} (s : X ⟶ Spec (.of R))

include hL in
/-- Properness and an ample line give common original affine charts for every full fiber. -/
theorem ampleAmbient_fiberSupport (J : RelativeIdealFamilies z d s) (x : X) :
    ∃ U : (allAffineAmbientCharts z).Index, ∀ y : J.val.subscheme,
      (J.val.subschemeι ≫ pullback.fst s z) y = x →
        (J.val.subschemeι ≫ pullback.snd s z) y ∈
          ((allAffineAmbientCharts z).chart U).opensRange := by
  obtain ⟨n, _, ⟨p⟩⟩ := hL.exists_power_presentation z
  exact projectiveAmbient_fiberSupport z p.embedding d s J x

/-- The constructed Hilbert scheme represents all full families in a proper ample ambient. -/
def ampleAmbientClassification :
    (allAffineAmbientCharts z).GluedParameters d s ≃ RelativeIdealFamilies z d s :=
  (allAffineAmbientCharts z).fiberSupportedClassification d s
    (ampleAmbient_fiberSupport z hL d s)

/-- The equivalence classifies the full family by actual universal pullback. -/
theorem ampleAmbientClassification_apply
    (p : (allAffineAmbientCharts z).GluedParameters d s) :
    ampleAmbientClassification z hL d s p =
      (allAffineAmbientCharts z).parameterFamily d s p := rfl

include hL in
/-- The proper ample application gives existence and uniqueness with no support premise. -/
theorem ampleAmbient_existsUnique_parameter (J : RelativeIdealFamilies z d s) :
    ∃! p : (allAffineAmbientCharts z).GluedParameters d s,
      (allAffineAmbientCharts z).parameterFamily d s p = J :=
  (allAffineAmbientCharts z).existsUnique_parameter_of_fiberSupport d s J
    (ampleAmbient_fiberSupport z hL d s J)

end FLT.Mazur.HilbertChart
