/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomSubgroupPullback
public import FLT.Mazur.CyclicOrbitCartierGenerator
public import FLT.Mazur.SmoothFiniteSubgroupAmple
public import FLT.Mazur.AmpleCyclicClassPresheaf
public import FLT.Mazur.OddWeierstrassCyclicHomLocusEquationUniversal

/-!
# Odd auxiliary chart: Actual ample cyclic moduli from the unrestricted source equation

Every zero of the full multiplication equation supplies an actual Cartier
generator and an ample subgroup of the original smooth source curve. The
resulting modular class commutes with arbitrary parameter change.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
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
    (WeierstrassIntegralChart.integralCurveStructure IntegralWeierstrassParameter.oddChartEquation)
      _)
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

end FLT.Mazur.OddWeierstrassParameter

/-!
# Odd auxiliary chart: The global cyclic locus maps naturally to actual modular classes

The constructed universal subgroup is cyclic and ample. Each test parameter
has the modular class of its actual reconstructed source, and this class is
the pullback of the universal object on the global closed locus.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual universal subgroup on the global locus is cyclic. -/
theorem cyclicHomUniversalSubgroup_isCyclic : (cyclicHomUniversalSubgroup n).IsCyclic :=
  cyclicHomSubgroup_isCyclic n _ _

/-- The actual universal Cartier subgroup on the global locus is ample. -/
theorem cyclicHomUniversalSubgroup_isAmple : (cyclicHomUniversalSubgroup n).IsAmple :=
  cyclicHomSubgroup_isAmple n _ _

/-- The modular class of the actual universal curve and subgroup on the closed locus. -/
def cyclicHomUniversalModuliClass :
    ampleCyclicClasses (cyclicHomUniversalMultiplicationLocus n) n :=
  cyclicHomSourceModuliClass n (cyclicHomUniversalMultiplicationLocusInclusion n)
    (cyclicHomUniversalLocus_equation_zero n)

/-- A test point of the global closed locus gives its actual source modular class. -/
def cyclicHomLocusModuliClass {T : Scheme} (q : T ⟶ cyclicHomUniversalMultiplicationLocus n) :
    ampleCyclicClasses T n :=
  cyclicHomSourceModuliClass n (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n)
    ((cyclicHomUniversalLocus_factorization_iff_equation n _).mp ⟨q, rfl⟩)

/-- The actual source class is obtained by pulling the universal curve and subgroup. -/
theorem cyclicHomLocusModuliClass_eq_pullback {T : Scheme}
    (q : T ⟶ cyclicHomUniversalMultiplicationLocus n) :
    cyclicHomLocusModuliClass n q =
      ampleCyclicClassesPullback q n (cyclicHomUniversalModuliClass n) :=
  cyclicHomSourceModuliClass_pullback n _ _ q

/-- The global locus-to-moduli map is natural under every test-scheme morphism. -/
theorem cyclicHomLocusModuliClass_natural {T U : Scheme}
    (q : T ⟶ cyclicHomUniversalMultiplicationLocus n) (k : U ⟶ T) :
    cyclicHomLocusModuliClass n (k ≫ q) =
      ampleCyclicClassesPullback k n (cyclicHomLocusModuliClass n q) := by
  simpa only [cyclicHomLocusModuliClass, Category.assoc] using!
    cyclicHomSourceModuliClass_pullback n (q ≫ cyclicHomUniversalMultiplicationLocusInclusion n)
      ((cyclicHomUniversalLocus_factorization_iff_equation n _).mp ⟨q, rfl⟩) k

end FLT.Mazur.OddWeierstrassParameter
