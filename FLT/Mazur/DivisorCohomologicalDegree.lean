/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CurveEulerCharacteristic
public import FLT.Mazur.DivisorSectionExact
public import FLT.Mazur.PrincipalSectionExtension
public import FLT.Mazur.ProperCoherentCohomology

/-!
# Cohomological degree of the canonical divisor cokernel

On a proper scheme over a field the canonical divisor sequence has finite
cohomology. If its actual cokernel has vanishing H¹, the Euler-characteristic
degree of O(D) is the dimension of that cokernel's H⁰. The identification of
this dimension with finite divisor length is not assumed or proved here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FCurve

variable {k : Type} [Field k] {X : Scheme}
  (f : X ⟶ Spec (CommRingCat.of k)) [IsProper f]
  {I : X.IdealSheafData} (hI : EffectiveCartier I)

include f in
/-- The canonical divisor cokernel is coherent, derived from its actual defining map. -/
theorem divisorSectionCokernel_isFinitePresentation :
    (cokernel (divisorSectionMap hI)).IsFinitePresentation := by
  have := Chow.source_isNoetherian f
  have : (structureModule X).IsFinitePresentation := unitSheaf_isFinitePresentation X
  have := hI.divisorLineBundle_locallyFreeRankOne.isFinitePresentation
  exact CoherentDevissage.coherent_cokernel (divisorSectionMap hI)

/-- The actual divisor cokernel has finite cohomology in every degree. -/
theorem divisorSectionCokernel_hasFiniteCohomology :
    HasFiniteCohomology f (cokernel (divisorSectionMap hI)) := by
  have := divisorSectionCokernel_isFinitePresentation f hI
  exact proper_coherent_hasFiniteCohomology f _

/-- Vanishing of the quotient's H¹ converts the divisor exact sequence into a degree formula. -/
theorem divisor_degree_eq_cokernel_h0
    [Subsingleton (ModuleScalarH f (cokernel (divisorSectionMap hI)) 1)] :
    curveSheafDegree f (divisorLineBundle I hI) =
      Module.finrank k (ModuleScalarH f (cokernel (divisorSectionMap hI)) 0) := by
  have := hI.divisorLineBundle_locallyFreeRankOne.isFinitePresentation
  have : (structureModule X).IsFinitePresentation := unitSheaf_isFinitePresentation X
  have h₁ := proper_coherent_hasFiniteCohomology f (structureModule X)
  have h₂ := proper_coherent_hasFiniteCohomology f (divisorLineBundle I hI)
  have h₃ := divisorSectionCokernel_hasFiniteCohomology f hI
  let S := divisorSectionComplex hI
  have : Subsingleton (ModuleScalarH f S.X₃ 1) :=
    inferInstanceAs (Subsingleton (ModuleScalarH f (cokernel (divisorSectionMap hI)) 1))
  have : Module.Finite k (ModuleScalarH f S.X₁ 0) := h₁ 0
  have : Module.Finite k (ModuleScalarH f S.X₁ 1) := h₁ 1
  have : Module.Finite k (ModuleScalarH f S.X₂ 0) := h₂ 0
  have : Module.Finite k (ModuleScalarH f S.X₂ 1) := h₂ 1
  have : Module.Finite k (ModuleScalarH f S.X₃ 0) := h₃ 0
  have he : Function.Surjective (moduleScalarHMap f S.g 1) := fun y ↦
    ⟨0, Subsingleton.elim _ _⟩
  have h := curveEulerCharacteristic_add_of_surjective f S
    (divisorSectionComplex_shortExact hI) he
  change curveEulerCharacteristic f (divisorLineBundle I hI) =
    curveEulerCharacteristic f (structureModule X) +
      curveEulerCharacteristic f (cokernel (divisorSectionMap hI)) at h
  change curveEulerCharacteristic f (divisorLineBundle I hI) -
    curveEulerCharacteristic f (structureModule X) = _
  rw [h, add_sub_cancel_left, curveEulerCharacteristic]
  simp only [Module.finrank_zero_of_subsingleton, Nat.cast_zero, sub_zero]

end FLT.Mazur.FCurve
