/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.FlatMonoSchematicClosure
public import FLT.Mazur.WeierstrassGenericKernelClosure
public import Mathlib.Algebra.Category.Ring.Instances

/-!
# The constructed kernel closure has the original generic fiber

The coefficient projection is a flat monomorphism for a fraction-field extension.
The exact original closed inclusion is therefore recovered from its schematic
integral closure, including its scheme structure and its structure map.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R K : Type} [CommRing R] [Field K] [Algebra R K]
  [IsFractionRing R K] (W : WeierstrassCurve R)

/-- The actual generic coefficient projection is flat. -/
instance integralCoefficientMorphism_fractionFlat :
    Flat (integralCoefficientMorphism (S := K) W) := by
  let _ : Flat (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    Flat.SpecMap_iff.mpr
      (RingHom.flat_algebraMap_iff.mpr (IsLocalization.flat K (nonZeroDivisors R)))
  exact MorphismProperty.of_isPullback (integralCoefficient_isPullback W).flip inferInstance

/-- Fraction-field base change is monomorphic on the actual glued cubic. -/
instance integralCoefficientMorphism_fractionMono :
    Mono (integralCoefficientMorphism (S := K) W) := by
  let _ : Epi (CommRingCat.ofHom (algebraMap R K)) :=
    IsLocalization.epi (nonZeroDivisors R) K
  let hm : Mono (CommRingCat.ofHom (algebraMap R K)).op := inferInstance
  let _ : Mono (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    (Functor.mono_map_iff_mono Scheme.Spec _).mpr hm
  exact (integralCoefficient_isPullback W).mono_fst_of_mono

variable {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K)))
  [IsClosedImmersion i]

/-- The original inclusion is the pullback of the actual integral closure inclusion. -/
theorem genericKernelClosureInclusion_isPullback :
    IsPullback (genericKernelToClosure W i) i (genericKernelClosureInclusion W i)
      (integralCoefficientMorphism W) := by
  let _ : QuasiCompact (integralCoefficientMorphism (S := K) W) :=
    MorphismProperty.of_isPullback (integralCoefficient_isPullback W).flip
      (inferInstanceAs (QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap R K)))))
  exact FLT.Mazur.FlatMonoSchematicClosure.closure_isPullback i (integralCoefficientMorphism W)

/-- The original scheme, with its original structure map, is the closure's generic fiber. -/
theorem genericKernelClosureStructure_isPullback :
    IsPullback (genericKernelToClosure W i)
      (i ≫ integralCurveStructure (W.map (algebraMap R K)))
      (genericKernelClosureStructure W i) (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  (genericKernelClosureInclusion_isPullback W i).paste_vert (integralCoefficient_isPullback W)

/-- A constructed isomorphism from the retained kernel to the actual generic fiber. -/
def genericKernelClosureGenericIso : H ≅
    pullback (genericKernelClosureStructure W i)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  (genericKernelClosureStructure_isPullback W i).isoPullback

/-- The generic-fiber isomorphism retains the original factorization into the closure. -/
@[reassoc] theorem genericKernelClosureGenericIso_fst :
    (genericKernelClosureGenericIso W i).hom ≫ pullback.fst _ _ = genericKernelToClosure W i :=
  (genericKernelClosureStructure_isPullback W i).isoPullback_hom_fst

/-- The generic-fiber isomorphism retains the original generic structure map. -/
@[reassoc] theorem genericKernelClosureGenericIso_snd :
    (genericKernelClosureGenericIso W i).hom ≫ pullback.snd _ _ =
      i ≫ integralCurveStructure (W.map (algebraMap R K)) :=
  (genericKernelClosureStructure_isPullback W i).isoPullback_hom_snd

end FLT.Mazur.WeierstrassIntegralChart
