/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomSubgroupPullback
public import FLT.Mazur.CyclicOrbitCartierGenerator

/-!
# Actual ample cyclic moduli from the unrestricted source equation

Every zero of the full multiplication equation supplies an actual Cartier
generator and an ample subgroup of the original smooth source curve. The
resulting modular class commutes with arbitrary parameter change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
  (h : cyclicHomMultiplicationEquation n f = 0)

/-- The unrestricted source is geometrically integral over its original base. -/
instance cyclicHomSourceCurve_geometricallyIntegral :
    GeometricallyIntegral (cyclicHomSourceCurve n f).curve.hom := by
  change GeometricallyIntegral (pullback.snd
    (WeierstrassIntegralChart.integralCurveStructure smoothEquation) _)
  infer_instance

/-- The actual orbit subgroup has a global Cartier generator. -/
theorem cyclicHomSubgroup_cartierGenerator :
    (cyclicHomSubgroup n f h).IsCartierGenerator
      ((cyclicHomSubgroup n f h).orbitGenerator (cyclicHomSourceMarking n f)
        (cyclicHomSubgroup_ideal n f h)) :=
  (cyclicHomSubgroup n f h).orbitGenerator_cartier _ (cyclicHomSubgroup_ideal n f h)

/-- The full source subgroup is cyclic even when its sections collide. -/
theorem cyclicHomSubgroup_isCyclic : (cyclicHomSubgroup n f h).IsCyclic :=
  (cyclicHomSubgroup_cartierGenerator n f h).isCyclic _

/-- Positive degree makes the actual cyclic Cartier subgroup ample on the source curve. -/
theorem cyclicHomSubgroup_isAmple : (cyclicHomSubgroup n f h).IsAmple :=
  (cyclicHomSubgroup n f h).isAmple_of_smooth (NeZero.pos n)
    (cyclicHomSubgroup_cartierGenerator n f h).2.1.1

/-- The exact full source data form an object of the intended ample cyclic moduli problem. -/
def cyclicHomSourceLevel : ampleCyclicLevels T n :=
  ⟨⟨cyclicHomSourceCurve n f, cyclicHomSubgroup n f h⟩,
    cyclicHomSubgroup_isCyclic n f h, cyclicHomSubgroup_isAmple n f h⟩

/-- The modular class of the actual full source curve and its orbit subgroup. -/
def cyclicHomSourceModuliClass : ampleCyclicClasses T n :=
  Quotient.mk _ (cyclicHomSourceLevel n f h)

/-- The actual source modular class commutes with arbitrary parameter change. -/
theorem cyclicHomSourceModuliClass_pullback (k : U ⟶ T) :
    cyclicHomSourceModuliClass n (k ≫ f) (cyclicHomMultiplicationEquation_zero_comp n f k h) =
      ampleCyclicClassesPullback k n (cyclicHomSourceModuliClass n f h) :=
  Quotient.sound ⟨cyclicHomSubgroupPullbackIso n f k h⟩

end FLT.Mazur.UniversalWeierstrass
