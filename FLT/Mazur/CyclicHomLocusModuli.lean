/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicHomSourceModuli
public import FLT.Mazur.CyclicHomLocusEquationUniversal

/-!
# The global cyclic locus maps naturally to actual modular classes

The constructed universal subgroup is cyclic and ample. Each test parameter
has the modular class of its actual reconstructed source, and this class is
the pullback of the universal object on the global closed locus.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
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

end FLT.Mazur.UniversalWeierstrass
