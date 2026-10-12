/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IndependentCyclicNormalizationGroup
public import FLT.Mazur.IndependentCyclicNormalizedSlice
public import FLT.Mazur.IndependentCyclicModuliPullback

/-!
# The independent closed slice retains the original modular object

Normalization compares the entire smooth curve and its Cartier cyclic subgroup.
The resulting map from the closed slice to the intended modular presheaf retains
the original class, with no coprimality condition on the cyclic order.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.UniversalWeierstrass
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n] {T : Scheme}
  (f : T ⟶ (independentCyclicAuxiliaryScheme n).left)
local notation "fN" => independentCyclicNormalizedPoint n f

/-- Normalization compares the whole independent source curves. -/
def independentCyclicNormalizationCurveIso :
    independentCyclicSourceCurve n fN ≅ independentCyclicSourceCurve n f := by
  let e : (independentCyclicSourceCurve n fN).group ≅ (independentCyclicSourceCurve n f).group :=
    (CommGrp.forget _).mapIso (independentCyclicNormalizationGroupIso n f)
  let _ : IsMonHom e.hom :=
    inferInstanceAs (IsMonHom (independentCyclicNormalizationGroupIso n f).hom.hom.hom.hom)
  exact isoOfSmoothGroup _ _ e

/-- The entire Cartier cyclic subgroup is retained by the full curve normalization. -/
def independentCyclicNormalizationSubgroupIso :
    CompatibleIso (independentCyclicSourceSubgroup n fN) (independentCyclicSourceSubgroup n f) :=
  relativeCyclicSubgroupCompatibleIso
    (E := independentCyclicSourceCurve n fN) (F := independentCyclicSourceCurve n f)
    (independentCyclicSourceMarking n fN) (independentCyclicSourceMarking n f)
    (independentCyclicSourceMarking_distinct n fN) (independentCyclicSourceMarking_distinct n f)
    (independentCyclicNormalizationCurveIso n f)
    (independentCyclicNormalizationGroupIso_marking n f)

/-- Normalization preserves the actual original ample cyclic modular class. -/
theorem independentCyclicSourceModuliClass_normalization :
    independentCyclicSourceModuliClass n fN = independentCyclicSourceModuliClass n f :=
  Quotient.sound ⟨independentCyclicNormalizationSubgroupIso n f⟩

/-- The independent closed normalized slice maps naturally to the intended modular presheaf. -/
def independentCyclicNormalizedModuliMap :
    yoneda.obj (independentCyclicNormalizedSlice n) ⋙ uliftFunctor.{1} ⟶
      ampleCyclicClassPresheaf n :=
  Functor.whiskerRight (yoneda.map (independentCyclicNormalizedSliceInclusion n))
    uliftFunctor.{1} ≫
    independentCyclicModuliMap n

/-- The actual normalized slice point represents precisely the original source object. -/
theorem independentCyclicNormalizedModuliMap_normalization :
    (independentCyclicNormalizedModuliMap n).app (Opposite.op T)
      (ULift.up (independentCyclicNormalizedSlicePoint n f)) =
        independentCyclicSourceModuliClass n f := by
  change independentCyclicSourceModuliClass n
    (independentCyclicNormalizedSlicePoint n f ≫ independentCyclicNormalizedSliceInclusion n) = _
  rw [independentCyclicNormalizedSlicePoint_inclusion,
    independentCyclicSourceModuliClass_normalization]

end FLT.Mazur.UniversalWeierstrass
