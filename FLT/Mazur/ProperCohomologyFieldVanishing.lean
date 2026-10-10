/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveDegreeFieldBaseChange
public import FLT.Mazur.ProperCoherentCohomology
public import FLT.Mazur.ProperCurveGenus

/-!
# Vanishing and genus under field extension

Proper line-bundle cohomology finiteness turns the existing dimension comparison into
preservation and detection of actual cohomology vanishing. The structure
sheaf comparison also preserves its Euler characteristic and curve genus.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

variable {k K : Type} [Field k] [Field K] {P X : Scheme}
  {p : P ⟶ X} {q : P ⟶ Spec (.of K)} {f : X ⟶ Spec (.of k)} [IsProper f]
  {g : Spec (.of K) ⟶ Spec (.of k)} (h : IsPullback p q f g)

include h in
/-- Field extension preserves and detects all proper line-bundle cohomology vanishing. -/
theorem proper_line_cohomology_field_vanishing_iff {M : X.Modules}
    (hM : LocallyFreeRankOne M)
    (n : ℕ) :
    Subsingleton (ModuleScalarH q ((pullback p).obj M) n) ↔
      Subsingleton (ModuleScalarH f M n) := by
  have : IsProper q := MorphismProperty.of_isPullback h inferInstance
  have := hM.isFinitePresentation
  have := (hM.pullback p).isFinitePresentation
  have := proper_coherent_hasFiniteCohomology f M n
  have := proper_coherent_hasFiniteCohomology q ((pullback p).obj M) n
  rw [← Module.finrank_zero_iff (R := K), ← Module.finrank_zero_iff (R := k),
    proper_field_cohomology_finrank h M n]

include h in
/-- The structure-sheaf Euler characteristic is invariant under every field extension. -/
theorem structure_euler_field_baseChange :
    curveEulerCharacteristic q (structureUnitModule P) =
      curveEulerCharacteristic f (structureUnitModule X) := by
  have := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  exact (curveEulerCharacteristic_iso q (modulePullbackUnitIso p)).symm.trans
    (curveEulerCharacteristic_field_baseChange h (structureModule X))

include h in
/-- Genus is unchanged after extending the field of a proper curve. -/
theorem curveGenus_field_baseChange [IsProper q]
    (hdX : topologicalKrullDim X = 1) (hcX : HasConstantGlobalSections f)
    (hdP : topologicalKrullDim P = 1) (hcP : HasConstantGlobalSections q) :
    curveGenus q hdP hcP = curveGenus f hdX hcX := by
  have := (structureModule_locallyFreeRankOne (X := X)).isFinitePresentation
  let he : ModuleScalarH q ((pullback p).obj (structureUnitModule X)) 1 ≃ₗ[K]
      ModuleScalarH q (structureUnitModule P) 1 :=
    ((moduleScalarHFunctor q 1).mapIso (modulePullbackUnitIso p)).toLinearEquiv
  change Module.finrank K (H1 q) = Module.finrank k (H1 f)
  rw [← (moduleScalarHUnitEquiv q 1).finrank_eq,
    ← (moduleScalarHUnitEquiv f 1).finrank_eq, ← he.finrank_eq]
  exact proper_field_cohomology_finrank h (structureModule X) 1

end FLT.Mazur.FCurve
