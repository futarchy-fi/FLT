/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AllAffineAmbientCharts
public import FLT.Mazur.ProjectiveFiniteAffineNeighborhood
public import FLT.Mazur.RelativeIdealFiniteFiberSupport
public import FLT.Mazur.AmbientHilbertClassificationNaturality

/-!
# Full Hilbert classification for closed projective ambients

Finite full fibers have a common affine neighborhood by homogeneous prime
avoidance. The atlas of all affine opens therefore represents every actual
finite locally free ideal family. No fiber-support premise remains.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open FLT.Mazur.ClosedIdealCover

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable {R : Type u} [CommRing R] {Z : Scheme.{u}} (z : Z ⟶ Spec (.of R))
variable {B : Type u} [CommRing B] {ι : Type u}
variable (e : Z ⟶ ProjectiveSpace.space B ι) [IsClosedImmersion e]
variable (d : ℕ) {X : Scheme.{u}} (s : X ⟶ Spec (.of R))

include e in
/-- Every full relative fiber lies in one chart of the constructed affine ambient atlas. -/
theorem projectiveAmbient_fiberSupport (J : RelativeIdealFamilies z d s) (x : X) :
    ∃ U : (allAffineAmbientCharts z).Index, ∀ y : J.val.subscheme,
      (J.val.subschemeι ≫ pullback.fst s z) y = x →
        (J.val.subschemeι ≫ pullback.snd s z) y ∈
          ((allAffineAmbientCharts z).chart U).opensRange := by
  obtain ⟨U, hU⟩ := ProjectiveSpace.exists_affineOpen_of_closed_embedding (R := B) (ι := ι) e
    (relativeIdealFiberSupport z d s J x) (relativeIdealFiberSupport_finite z d s J x)
  refine ⟨U, ?_⟩
  rw [allAffineAmbientCharts_opensRange]
  exact (relativeIdealFiberSupport_subset_iff z d s J x U.val).mp hU

variable [IsSeparated z]

/-- A closed projective ambient has full finite-family classification on every test scheme. -/
def projectiveAmbientClassification :
    (allAffineAmbientCharts z).GluedParameters d s ≃ RelativeIdealFamilies z d s :=
  (allAffineAmbientCharts z).fiberSupportedClassification d s
    (projectiveAmbient_fiberSupport z e d s)

/-- Classification is actual universal pullback of the entire ideal family. -/
theorem projectiveAmbientClassification_apply
    (p : (allAffineAmbientCharts z).GluedParameters d s) :
    projectiveAmbientClassification z e d s p =
      (allAffineAmbientCharts z).parameterFamily d s p := rfl

include e in
/-- Every full family has a unique actual classifying morphism, with no support assumption. -/
theorem projectiveAmbient_existsUnique_parameter (J : RelativeIdealFamilies z d s) :
    ∃! p : (allAffineAmbientCharts z).GluedParameters d s,
      (allAffineAmbientCharts z).parameterFamily d s p = J :=
  (allAffineAmbientCharts z).existsUnique_parameter_of_fiberSupport d s J
    (projectiveAmbient_fiberSupport z e d s J)

end FLT.Mazur.HilbertChart
