/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module
public import FLT.Mazur.IndependentCyclicSourceGroupPullback
/-!
# Independent cyclic modular data commute with source change
The actual source group comparison extends to the whole smooth curve and its
Cartier subgroup. Thus the independent chart defines a natural map to the
intended ample cyclic moduli presheaf, at every positive cyclic order.
-/
@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T U : Scheme}
  (f : T ⟶ (independentCyclicAuxiliaryScheme n).left) (k : U ⟶ T)
/-- The whole independent source curve is the actual pullback of the original one. -/
def independentCyclicSourceCurvePullbackIso :
    (independentCyclicSourceCurve n f).baseChange k ≅
      independentCyclicSourceCurve n (k ≫ f) := by
  let _ : Smooth ((independentCyclicSourceCurve n f).baseChange k).curve.hom :=
    inferInstanceAs (Smooth (pullback.snd (independentCyclicSourceCurve n f).curve.hom k))
  let e : ((independentCyclicSourceCurve n f).baseChange k).group ≅
      (independentCyclicSourceCurve n (k ≫ f)).group :=
    (CommGrp.forget _).mapIso (independentCyclicSourceGroupIso n f k)
  let _ : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (independentCyclicSourceGroupIso n f k).hom.hom.hom.hom)
  exact isoOfSmoothGroup _ _ e
/-- Source change retains the full original cyclic subgroup, not only its generator. -/
def independentCyclicSourceSubgroupPullbackIso :
    CompatibleIso (independentCyclicSourceSubgroup n (k ≫ f))
      ((independentCyclicSourceSubgroup n f).baseChange k) :=
  (relativeCyclicSubgroupCompatibleIso
    (E := (independentCyclicSourceCurve n f).baseChange k)
    (F := independentCyclicSourceCurve n (k ≫ f))
    (pullCyclicMarking (E := independentCyclicSourceCurve n f)
      k (independentCyclicSourceMarking n f))
    (independentCyclicSourceMarking n (k ≫ f))
    (pullCyclicMarking_distinct (E := independentCyclicSourceCurve n f)
      k _ (independentCyclicSourceMarking_distinct n f))
    (independentCyclicSourceMarking_distinct n (k ≫ f))
    (independentCyclicSourceCurvePullbackIso n f k)
    (independentCyclicSourceGroupIso_marking n f k)).symm.trans
      (pullCyclicMarkingCompatibleIso (E := independentCyclicSourceCurve n f)
      k _ (independentCyclicSourceMarking_distinct n f))
/-- Independent source modular classes commute with arbitrary base change. -/
theorem independentCyclicSourceModuliClass_pullback :
    independentCyclicSourceModuliClass n (k ≫ f) =
      ampleCyclicClassesPullback k n (independentCyclicSourceModuliClass n f) :=
  Quotient.sound ⟨independentCyclicSourceSubgroupPullbackIso n f k⟩
/-- Forget both markings while retaining the actual original ample cyclic modular object. -/
def independentCyclicModuliMap :
    yoneda.obj (independentCyclicAuxiliaryScheme n).left ⋙ uliftFunctor.{1} ⟶
      ampleCyclicClassPresheaf n where
  app T := ↾(fun p ↦ independentCyclicSourceModuliClass n (T := T.unop) p.down)
  naturality T U g := by
    apply ConcreteCategory.hom_ext
    intro p
    exact independentCyclicSourceModuliClass_pullback n p.down g.unop
end FLT.Mazur.UniversalWeierstrass
