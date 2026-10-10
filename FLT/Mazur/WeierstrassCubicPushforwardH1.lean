/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicExactSequence
public import FLT.Mazur.WeierstrassCubicAmbientCohomology
public import FLT.Mazur.ModuleRingCohomologyExact

/-!
# The first cohomology of the actual cubic pushforward

The short exact cubic sequence and ambient vanishing make its connecting map
an isomorphism H1(i_*O_C) ≃ H2(O(-3)). The existing exponent calculation then
identifies this genuine cohomology group with the base ring, retaining scalars.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open FLT.Mazur.ProjectiveSpace FLT.Mazur.ProjectiveSpace.LocalizationDegree
open FLT.Mazur.FCurve FLT.Mazur.WeierstrassCubicAmbientCohomology

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R]

/-- Actual positive structure cohomology of the plane vanishes with its base-ring action. -/
theorem cubicAmbientStructure_positive_zero (q : ℕ) :
    Subsingleton (ModuleRingH (constantSection R (Fin 3) ⊤)
      (structureModule (space R (Fin 3))) (q + 1)) := by
  let _ : Subsingleton ((moduleRingHFunctor (constantSection R (Fin 3) ⊤)
      (q + 1)).obj (twistingSheaf R (Fin 3) 0)) := planeUntwisted_positive_zero R q
  exact (((moduleRingHFunctor (constantSection R (Fin 3) ⊤) (q + 1)).mapIso
    (twistingSheafZeroIso R (Fin 3))).toLinearEquiv).surjective.subsingleton

variable [IsDomain R] (W : WeierstrassCurve R)

/-- The connecting map is injective because ambient H1(O) vanishes. -/
theorem cubicH1Connecting_injective :
    Function.Injective (moduleRingHConnecting (constantSection R (Fin 3) ⊤)
      (cubicStructureComplex W) (cubicStructureComplex_shortExact W) 1) := by
  let _ : Subsingleton ((moduleRingHFunctor (constantSection R (Fin 3) ⊤)
      1).obj (cubicStructureComplex W).X₂) := cubicAmbientStructure_positive_zero 0
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  obtain ⟨y, hy⟩ := (moduleRingH_exact_right (constantSection R (Fin 3) ⊤)
    (cubicStructureComplex W) (cubicStructureComplex_shortExact W) 1 x).mp hx
  have hy0 : y = 0 := Subsingleton.elim _ _
  rw [hy0, map_zero] at hy
  exact hy.symm

/-- The connecting map is surjective because ambient H2(O) vanishes. -/
theorem cubicH1Connecting_surjective :
    Function.Surjective (moduleRingHConnecting (constantSection R (Fin 3) ⊤)
      (cubicStructureComplex W) (cubicStructureComplex_shortExact W) 1) := by
  let _ : Subsingleton ((moduleRingHFunctor (constantSection R (Fin 3) ⊤)
      2).obj (cubicStructureComplex W).X₂) := cubicAmbientStructure_positive_zero 1
  intro x
  exact (moduleRingH_exact_left (constantSection R (Fin 3) ⊤)
    (cubicStructureComplex W) (cubicStructureComplex_shortExact W) 1 x).mp
      (Subsingleton.elim _ _)

/-- The actual connecting homomorphism is a base-linear equivalence. -/
def cubicH1ConnectingEquiv :
    ModuleRingH (constantSection R (Fin 3) ⊤) (cubicStructurePushforward W) 1 ≃ₗ[R]
      ModuleRingH (constantSection R (Fin 3) ⊤) (twistingSheaf R (Fin 3) (-3)) 2 :=
  LinearEquiv.ofBijective (moduleRingHConnecting (constantSection R (Fin 3) ⊤)
    (cubicStructureComplex W) (cubicStructureComplex_shortExact W) 1)
    ⟨cubicH1Connecting_injective W, cubicH1Connecting_surjective W⟩

/-- The first cohomology of the genuine cubic pushforward is free of rank one. -/
def cubicPushforwardH1Equiv :
    ModuleRingH (constantSection R (Fin 3) ⊤) (cubicStructurePushforward W) 1 ≃ₗ[R] R :=
  (cubicH1ConnectingEquiv W).trans (cubicNegativeTwistH2Equiv R)

/-- Over a field this cohomology has dimension one, including for singular cubics. -/
theorem cubicPushforwardH1_finrank {K : Type} [Field K] (E : WeierstrassCurve K) :
    Module.finrank K (ModuleRingH (constantSection K (Fin 3) ⊤)
      (cubicStructurePushforward E) 1) = 1 :=
  (cubicPushforwardH1Equiv E).finrank_eq.trans (Module.finrank_self K)

end FLT.Mazur.WeierstrassIntegralChart
