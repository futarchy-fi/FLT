/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OddWeierstrassCyclicHomNormalizedLocus
public import FLT.Mazur.OddWeierstrassCyclicHomSourceModuli

/-!
# The normalized actual subgroup locus maps to the modular presheaf

The locus map is natural on all test schemes. The normalized point of an
original subgroup parameter represents exactly its original modular class,
including when the cyclic sections coincide.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.OddWeierstrassParameter
open UniversalWeierstrass (Labels)
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual subgroup locus defines a natural map to ample cyclic modular classes. -/
def cyclicHomLocusModuliMap :
    yoneda.obj (cyclicHomUniversalMultiplicationLocus n) ⋙ uliftFunctor.{1} ⟶
      ampleCyclicClassPresheaf n where
  app T := ↾(fun p ↦ cyclicHomLocusModuliClass n (T := T.unop) p.down)
  naturality T U g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact cyclicHomLocusModuliClass_natural n p.down g.unop

/-- The closed normalized subgroup locus defines its actual natural modular map. -/
def cyclicHomNormalizedModuliMap :
    yoneda.obj (cyclicHomNormalizedLocus n) ⋙ uliftFunctor.{1} ⟶ ampleCyclicClassPresheaf n :=
  Functor.whiskerRight (yoneda.map (cyclicHomNormalizedLocusInclusion n)) uliftFunctor.{1} ≫
    cyclicHomLocusModuliMap n

/-- The normalized actual subgroup represents precisely the original full modular object. -/
theorem cyclicHomNormalizedModuliMap_normalization {T : Scheme}
    (f : T ⟶ (cyclicHomAuxiliaryScheme n).left)
    (h : cyclicHomMultiplicationEquation n f = 0) :
    (cyclicHomNormalizedModuliMap n).app (Opposite.op T)
      (ULift.up (cyclicHomNormalizedLocusPoint n f h)) = cyclicHomSourceModuliClass n f h := by
  change cyclicHomSourceModuliClass n
    ((cyclicHomNormalizedLocusPoint n f h ≫ cyclicHomNormalizedLocusInclusion n) ≫
      cyclicHomUniversalMultiplicationLocusInclusion n) _ = _
  simp only [Category.assoc, cyclicHomNormalizedLocusPoint_parameter]
  exact cyclicHomSourceModuliClass_normalization n f h

end FLT.Mazur.OddWeierstrassParameter
