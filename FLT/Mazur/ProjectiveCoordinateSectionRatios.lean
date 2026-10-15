/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveCoordinateGeneratorOpen
public import FLT.Mazur.ModuleSectionRatioOpenNaturality

/-!
# Ratios of the actual homogeneous coordinate sections

The cocycle coordinates compute the ratios of the global hyperplane sections.
The formula also computes their pullbacks on arbitrary source subopens.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Scheme.Modules
namespace FLT.Mazur.ProjectiveSpace
open FCurve ModuleSheafUnitCocycle
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local instance] MvPolynomial.gradedAlgebra
universe u
variable (R : Type u) [CommRing R] (ι : Type u)

/-- The actual ratio of two homogeneous sections is the original chart coordinate. -/
theorem coordinateGlobalSection_ratio (i j : ι) (U : (space R ι).Opens)
    (hU : U ≤ chart R ι j) :
    sectionRatioOn (twistingSheaf R ι 1) (coordinateGlobalSection R ι j) U
        (hU.trans (coordinateGlobalSection_generatorOpen R ι j).symm.le)
        (coordinateGlobalSection R ι i) = res hU (chartCoordinateSection R ι j i) := by
  apply (sectionRatioOn_eq_iff _ _ _ _ _ _).mpr
  apply ((twistCocycle R ι 1).evaluationEquiv j hU).injective
  change (twistCocycle R ι 1).evaluate j hU
    (res hU (chartCoordinateSection R ι j i) •
      (twistCocycle R ι 1).restrict le_top (coordinateGlobalSection R ι j)) =
    (twistCocycle R ι 1).evaluate j hU
      ((twistCocycle R ι 1).restrict le_top (coordinateGlobalSection R ι i))
  rw [Cocycle.evaluate_smul, coordinateGlobalSection_evaluate,
    coordinateGlobalSection_evaluate, chartCoordinateSection_self, map_one, mul_one]

/-- Homogeneous coordinates generate the hyperplane line over every coefficient ring. -/
theorem coordinateGlobalSections_cover :
    (⨆ i, sectionGeneratorOpen (twistingSheaf R ι 1)
      (coordinateGlobalSection R ι i)) = ⊤ := by
  simp only [coordinateGlobalSection_generatorOpen, iSup_chart]

/-- Pulling the coordinate sections back retains their actual regular chart ratios. -/
theorem coordinateGlobalSection_pullback_ratio {X : Scheme.{u}} (f : X ⟶ space R ι)
    (i j : ι) (V : X.Opens) (hV : V ≤ f ⁻¹ᵁ chart R ι j)
    (hj : V ≤ sectionGeneratorOpen ((pullback f).obj (twistingSheaf R ι 1))
      (pullGlobal f (twistingSheaf R ι 1) (coordinateGlobalSection R ι j))) :
    sectionRatioOn ((pullback f).obj (twistingSheaf R ι 1))
        (pullGlobal f (twistingSheaf R ι 1) (coordinateGlobalSection R ι j)) V hj
        (pullGlobal f (twistingSheaf R ι 1) (coordinateGlobalSection R ι i)) =
      f.appLE (chart R ι j) V hV (chartCoordinateSection R ι j i) := by
  rw [← sectionRatioOn_pullback f (twistingSheaf R ι 1) (chart R ι j) V hV
    _ _ (coordinateGlobalSection_generatorOpen R ι j).symm.le hj,
    coordinateGlobalSection_ratio R ι i j _ le_rfl, res_self]

end FLT.Mazur.ProjectiveSpace
