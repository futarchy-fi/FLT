/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HomogeneousLocalizationGenerator
public import FLT.Mazur.SectionGradedPowerRatios

/-!
# The section ring on a generator open

On a generator subopen, powers of the generating section freely generate
the corresponding homogeneous pieces. The homogeneous localization of
the restricted section ring is therefore the actual ring of functions.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry HomogeneousLocalization
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedGeneratorLocalization
open FCurve ModuleLineBundleTensorPullback SectionGradedMultiplication SectionGradedSum
open SectionGradedPowerGenerators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) [hL : Fact (LocallyFreeRankOne L)]
  (d : ℕ) (s : Piece L ⊤ d) (U : X.Opens)
  (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s)

include hU

/-- Restricted powers of a generator detect scalars on every subopen. -/
lemma power_smul_injective (n : ℕ) :
    Function.Injective (fun a : Γ(X, U) ↦ a •
      (restrictRingHom L U U.leTop (of L ⊤ d s)) ^ n) := by
  intro a b h
  rw [← map_pow, ← of_powerSection] at h
  change a • restrict L U.leTop (of L ⊤ (d * n) (powerSection L d s n)) =
    b • restrict L U.leTop (of L ⊤ (d * n) (powerSection L d s n)) at h
  rw [restrict_of] at h
  have he : of L U (d * n) (a • (tensorPower L (d * n)).presheaf.map U.leTop.op
      (powerSection L d s n)) = of L U (d * n) (b •
        (tensorPower L (d * n)).presheaf.map U.leTop.op (powerSection L d s n)) := by
    simpa only [_root_.map_smul] using h
  exact smul_powerSection_injective L hL.out d s n U hU (DirectSum.of_injective (d * n) he)

/-- Every homogeneous section of the matching degree is a scalar times the generator power. -/
lemma power_generates (n : ℕ) (z : SectionGradedSum.Sections L U)
    (hz : z ∈ grade L U (n • d)) :
    ∃ a : Γ(X, U), z = a • (restrictRingHom L U U.leTop (of L ⊤ d s)) ^ n := by
  rw [nsmul_eq_mul, Nat.mul_comm] at hz
  obtain ⟨t, rfl⟩ := hz
  let := sectionGeneratorOpen_app_isIso (tensorPower L (d * n)) (powerSection L d s n) U
    (hU.trans (le_generatorOpen_powerSection L hL.out d s n))
  obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso
    ((globalSectionHom _ (powerSection L d s n)).app U)).surjective t
  change Γ(X, U) at a
  change a • (tensorPower L (d * n)).presheaf.map U.leTop.op (powerSection L d s n) = t at ha
  refine ⟨a, ?_⟩
  rw [← map_pow, ← of_powerSection]
  change of L U (d * n) t = a • restrict L U.leTop (of L ⊤ (d * n) (powerSection L d s n))
  rw [restrict_of, ← (of L U (d * n)).map_smul, ha]

/-- The scalar ring is canonically the homogeneous localization on a generator subopen. -/
def scalarEquiv : Γ(X, U) ≃+* Away (grade L U)
    (restrictRingHom L U U.leTop (of L ⊤ d s)) :=
  HomogeneousLocalizationGenerator.scalarEquiv (grade L U)
    (show restrictRingHom L U U.leTop (of L ⊤ d s) ∈ grade L U d from
      ⟨_, (restrict_of L U.leTop d s).symm⟩)
    (power_smul_injective L d s U hU) (power_generates L d s U hU)

end FLT.Mazur.SectionGradedGeneratorLocalization
