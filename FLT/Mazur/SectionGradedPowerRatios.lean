/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SectionGradedPowerGenerators
public import FLT.Mazur.SectionGradedRestriction

/-!
# Ratios with a power-section denominator

A section in degree `d * n` is a scalar multiple of the `n`th power of a
chosen degree-`d` generator on its chart. These coefficients restrict
naturally, and vanish wherever the numerator vanishes.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
namespace FLT.Mazur.SectionGradedPowerRatios
open FCurve ModuleLineBundleTensorPullback SectionGradedSum SectionGradedMultiplication
open SectionGradedPowerGenerators
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X : Scheme.{u}} (L : X.Modules) (hL : LocallyFreeRankOne L)
  (d : ℕ) (s : Piece L ⊤ d) (n : ℕ)

/-- Coefficient of a section relative to a homogeneous power on a generator subopen. -/
def coefficient (U : X.Opens) (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s)
    (t : Piece L ⊤ (d * n)) : Γ(X, U) :=
  sectionRatioOn (tensorPower L (d * n)) (powerSection L d s n) U
    (hU.trans (le_generatorOpen_powerSection L hL d s n)) t

/-- The coefficient times the actual ring power equals the restricted numerator. -/
lemma coefficient_smul (U : X.Opens) (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s)
    (t : Piece L ⊤ (d * n)) :
    coefficient L hL d s n U hU t •
      (restrictRingHom L U U.leTop (of L ⊤ d s)) ^ n =
        restrictRingHom L U U.leTop (of L ⊤ (d * n) t) := by
  rw [← map_pow, ← of_powerSection, show restrictRingHom L U U.leTop
      (of L ⊤ (d * n) (powerSection L d s n)) =
      of L U (d * n) ((tensorPower L (d * n)).presheaf.map U.leTop.op
        (powerSection L d s n)) from restrict_of L _ _ _]
  rw [← _root_.map_smul]
  have he := sectionRatioOn_smul (tensorPower L (d * n)) (powerSection L d s n) U
    (hU.trans (le_generatorOpen_powerSection L hL d s n)) t
  change coefficient L hL d s n U hU t •
    (tensorPower L (d * n)).presheaf.map U.leTop.op (powerSection L d s n) =
      (tensorPower L (d * n)).presheaf.map U.leTop.op t at he
  rw [he]
  exact (restrict_of L _ _ _).symm

/-- Coefficients restrict to the same power-section ratios on smaller opens. -/
lemma coefficient_restrict {U V : X.Opens} (hVU : V ≤ U)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) (t : Piece L ⊤ (d * n)) :
    X.presheaf.map (homOfLE hVU).op (coefficient L hL d s n U hU t) =
      coefficient L hL d s n V (hVU.trans hU) t :=
  sectionRatioOn_restrict _ _ _ _ _ _ _

/-- A power-section coefficient vanishes wherever its numerator vanishes. -/
lemma coefficient_eq_zero (U : X.Opens)
    (hU : U ≤ sectionGeneratorOpen (tensorPower L d) s) (t : Piece L ⊤ (d * n))
    (ht : (tensorPower L (d * n)).presheaf.map U.leTop.op t = 0) :
    coefficient L hL d s n U hU t = 0 := by
  apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
  rw [zero_smul]
  exact ht.symm

end FLT.Mazur.SectionGradedPowerRatios
