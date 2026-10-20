/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicCoarseUniversal
public import FLT.Mazur.CyclicCharacteristicLocalModuliSheafDescent

/-!
# The coarse transformation on original locally normalized modular classes

The constructed transformation and its scheme-valued universal property apply
to the original local modular image, which includes every smooth ample cyclic
family. No coverage of singular families is assumed or asserted.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The actual coarse map on original classes admitting parameters fppf locally. -/
def localModuliCoarseTransformation : (locallyNormalizedModuli n).toFunctor ⟶
    uliftYoneda.{1}.obj (invariantOrbitScheme n) :=
  locallyNormalizedModuliMap n ≫ (normalizedCoarseTransformation n).hom

/-- Original pointwise classes retain their constructed coarse image. -/
@[reassoc] theorem localModuliCoarseTransformation_classes :
    unmarkedClassToLocalModuli n ≫ localModuliCoarseTransformation n =
      unmarkedClassToSheaf n ≫ (normalizedCoarseTransformation n).hom := by
  exact unmarkedClassToLocalModuli_map_assoc n _

/-- Every original normalized parameter retains its actual chart morphism. -/
theorem localModuliCoarseTransformation_parameters :
    unmarkedParameterProjection n ≫ unmarkedClassToLocalModuli n ≫
      localModuliCoarseTransformation n = schemeParameterMap n (normalizedCoarseChart n) := by
  rw [localModuliCoarseTransformation_classes, ← Category.assoc]
  exact normalizedCoarseTransformation_parameters n

variable {Y : Scheme} (t : (locallyNormalizedModuli n).toFunctor ⟶ uliftYoneda.{1}.obj Y)

/-- Descend any scheme-valued transformation on the original local modular image. -/
def localModuliCoarseDescend : invariantOrbitScheme n ⟶ Y :=
  normalizedCoarseDescend n
    (localModuliSheafDesc n (F := Scheme.fppfTopology.uliftYoneda.{1}.obj Y) t)

/-- The descended scheme map recovers the transformation on all original local classes. -/
theorem localModuliCoarseDescend_fac :
    localModuliCoarseTransformation n ≫ uliftYoneda.map (localModuliCoarseDescend n t) = t := by
  have h := congrArg (fun d ↦ locallyNormalizedModuliMap n ≫ d.hom)
    (normalizedCoarseDescend_fac n
      (localModuliSheafDesc n (F := Scheme.fppfTopology.uliftYoneda.{1}.obj Y) t))
  change locallyNormalizedModuliMap n ≫ ((normalizedCoarseTransformation n).hom ≫
    uliftYoneda.map (localModuliCoarseDescend n t)) = _ at h
  rw [← Category.assoc] at h
  exact h.trans (localModuliSheafDesc_fac n
    (F := Scheme.fppfTopology.uliftYoneda.{1}.obj Y) t)

/-- The transformation on original locally normalized classes determines its scheme factor. -/
theorem localModuliCoarseDescend_unique (g : invariantOrbitScheme n ⟶ Y)
    (hg : localModuliCoarseTransformation n ≫ uliftYoneda.map g = t) :
    g = localModuliCoarseDescend n t := by
  apply normalizedCoarseDescend_unique
  apply localModuliSheaf_hom_ext n
  change locallyNormalizedModuliMap n ≫ ((normalizedCoarseTransformation n).hom ≫
    uliftYoneda.map g) = _
  rw [← Category.assoc]
  exact hg.trans (localModuliSheafDesc_fac n
    (F := Scheme.fppfTopology.uliftYoneda.{1}.obj Y) t).symm

/-- Universality holds on the original local modular image for every scheme target. -/
theorem localModuliCoarse_universal :
    ∃! g : invariantOrbitScheme n ⟶ Y,
      localModuliCoarseTransformation n ≫ uliftYoneda.map g = t :=
  ⟨localModuliCoarseDescend n t, localModuliCoarseDescend_fac n t,
    fun g hg ↦ localModuliCoarseDescend_unique n t g hg⟩

end FLT.Mazur.CyclicCharacteristicOrbit
