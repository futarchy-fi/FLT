/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalWeierstrassCyclicSourceModuliPullback

/-!
# The represented full chart maps naturally to the intended modular presheaf

The map forgets auxiliary labels and the choice of a cyclic generator, but
retains the actual original generalized curve and its ample Cartier subgroup.
It asserts neither coverage of arbitrary modular objects nor injectivity after
forgetting these markings.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve.FiniteSubgroup
variable (n : ℕ) [NeZero n]

/-- Forget full labels naturally while retaining the original actual ample cyclic data. -/
def cyclicMarkedFamilyClassModuliMap :
    cyclicMarkedFamilyClassPresheaf n ⋙ uliftFunctor.{1} ⟶ ampleCyclicClassPresheaf n where
  app T := ↾(fun q ↦ cyclicMarkedFamilyClassesToModuli n (T := T.unop) q.down)
  naturality _ _ k := by
    apply ConcreteCategory.hom_ext
    intro q
    exact cyclicMarkedFamilyClassesToModuli_natural n k.unop q.down

/-- The original full closed slice maps to the intended moduli presheaf. -/
def cyclicNormalizedSliceModuliMap :
    yoneda.obj (cyclicNormalizedSlice n) ⋙ uliftFunctor.{1} ⟶ ampleCyclicClassPresheaf n :=
  (Functor.isoWhiskerRight (cyclicMarkedFamilyClassRepresentation n) uliftFunctor.{1}).inv ≫
    cyclicMarkedFamilyClassModuliMap n

/-- Normalization retains the actual ample cyclic class of each original chart point. -/
theorem cyclicNormalizedSliceModuliMap_normalization {T : Scheme}
    (f : T ⟶ (cyclicAuxiliaryScheme n).left) :
    (cyclicNormalizedSliceModuliMap n).app (Opposite.op T)
      (ULift.up (f ≫ cyclicNormalizationSliceMap n)) = cyclicSourceModuliClass n f := by
  exact congrArg (cyclicMarkedFamilyClassesToModuli n)
    ((cyclicMarkedFamilyClassesEquiv n T).left_inv (Quotient.mk _ f))

/-- The split full slice carries actual ample cyclic modular data. -/
def cyclicNormalizedSliceModuliClass : ampleCyclicClasses (cyclicNormalizedSlice n) n :=
  (cyclicNormalizedSliceModuliMap n).app (Opposite.op _) (ULift.up (𝟙 _))

end FLT.Mazur.UniversalWeierstrass
