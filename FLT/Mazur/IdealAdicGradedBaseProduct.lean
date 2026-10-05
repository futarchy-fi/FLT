/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicGradedPullback
public import FLT.Mazur.IdealAdicGradedRing

/-!
# Products under the base associated-graded comparison

The canonical comparison preserves multiplication of ideal-power sections.
On affine base opens every graded section has a representative, so the
comparison preserves the actual graded products there as well.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.IdealAdicQuotient
open ModuleSheafTensor FLT.Mazur.CoherentIdealIntersection

universe u

namespace FLT.Mazur.IdealAdicGradedPullback

variable {X Y : Scheme.{u}} (J : Y.IdealSheafData) (f : X ⟶ Y)

/-- Pull a graded section into the actual extended-ideal graded piece. -/
def pull (n : ℕ) (U : Y.Opens) (s : IdealAdicGradedSections.Piece J U n) :
    IdealAdicGradedSections.Piece (J.comap f) (f ⁻¹ᵁ U) n := (gradedMap J f n).app U s

/-- The section comparison is induced by the map of original ideal powers. -/
lemma pull_projection (n : ℕ) (U : Y.Opens) (s : Γ(idealModule (J ^ n), U)) :
    pull J f n U ((cokernel.π (idealStep J n)).app U s) =
      (cokernel.π (idealStep (J.comap f) n)).app (f ⁻¹ᵁ U)
        ((powerMap J f n).app U s) :=
  congrArg (fun k ↦ k.app U s) (gradedMap_projection J f n)

variable [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

/-- Extension respects multiplication of the original ideal-power sections. -/
lemma powerMap_mul (a b : ℕ) (U : Y.Opens)
    (s : Γ(idealModule (J ^ a), U)) (t : Γ(idealModule (J ^ b), U)) :
    (powerMap J f (a + b)).app U ((idealPowerMul J a b).app U (pure _ _ U s t)) =
      (idealPowerMul (J.comap f) a b).app (f ⁻¹ᵁ U)
        (pure _ _ (f ⁻¹ᵁ U) ((powerMap J f a).app U s) ((powerMap J f b).app U t)) := by
  apply ModuleSubobjectCoverEquality.app_injective
    (idealModuleι (J.comap f ^ (a + b))) (f ⁻¹ᵁ U)
  rw [powerMap_inclusion, idealPowerMul_pure, idealPowerMul_pure,
    powerMap_inclusion, powerMap_inclusion]
  exact (f.app U).hom.map_mul _ _

/-- The graded section product is the quotient of the original ideal-power product. -/
lemma mul_projection (a b : ℕ) (U : Y.Opens)
    (s : Γ(idealModule (J ^ a), U)) (t : Γ(idealModule (J ^ b), U)) :
    IdealAdicGradedSections.mul J U a b ((cokernel.π (idealStep J a)).app U s)
      ((cokernel.π (idealStep J b)).app U t) =
        (cokernel.π (idealStep J (a + b))).app U
          ((idealPowerMul J a b).app U (pure _ _ U s t)) := by
  exact idealGradedMul_pure J a b U s t

/-- On affine base opens the comparison preserves products of all graded sections. -/
lemma pull_mul (a b : ℕ) (U : Y.affineOpens)
    (s : IdealAdicGradedSections.Piece J U.1 a)
    (t : IdealAdicGradedSections.Piece J U.1 b) :
    pull J f (a + b) U.1 (IdealAdicGradedSections.mul J U.1 a b s t) =
      IdealAdicGradedSections.mul (J.comap f) (f ⁻¹ᵁ U.1) a b
        (pull J f a U.1 s) (pull J f b U.1 t) := by
  have := idealModule_coherent (J ^ a)
  have := idealModule_coherent (J ^ b)
  have : (cokernel (idealStep J a)).IsFinitePresentation := idealGraded_coherent J a
  have : (cokernel (idealStep J b)).IsFinitePresentation := idealGraded_coherent J b
  obtain ⟨s, rfl⟩ := GlobalIdealPower.affine_epi_surjective (cokernel.π (idealStep J a)) U s
  obtain ⟨t, rfl⟩ := GlobalIdealPower.affine_epi_surjective (cokernel.π (idealStep J b)) U t
  rw [mul_projection, pull_projection, pull_projection, pull_projection, mul_projection,
    powerMap_mul]

omit [IsLocallyNoetherian X] [IsLocallyNoetherian Y] in
/-- The comparison preserves the degree-zero scalar map. -/
lemma pull_scalar (U : Y.Opens) (r : Γ(Y, U)) :
    pull J f 0 U (IdealAdicGradedSections.scalar J U r) =
      IdealAdicGradedSections.scalar (J.comap f) (f ⁻¹ᵁ U) (f.app U r) := by
  change pull J f 0 U ((cokernel.π (idealStep J 0)).app U
    ((idealPowerZeroIso J).inv.app U r)) =
      (cokernel.π (idealStep (J.comap f) 0)).app (f ⁻¹ᵁ U)
        ((idealPowerZeroIso (J.comap f)).inv.app (f ⁻¹ᵁ U) (f.app U r))
  rw [pull_projection]
  congr 1
  apply ModuleSubobjectCoverEquality.app_injective
    (idealModuleι (J.comap f ^ 0)) (f ⁻¹ᵁ U)
  rw [powerMap_inclusion, idealPowerZeroIso_inv_app, idealPowerZeroIso_inv_app]

end FLT.Mazur.IdealAdicGradedPullback
