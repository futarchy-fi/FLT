/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassGenericClosureSmoothDensity
public import FLT.Mazur.WeierstrassGenericKernelRecovery

/-!
# Exact generic recovery from the same closure's smooth intersection

Removing the nonsmooth part of the integral cubic does not change the generic
kernel when the generic cubic is smooth. The Cartesian square retains the
original inclusion and structure map, with no claim of integral finiteness.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]

/-- The same original kernel is exactly the generic fiber of the smooth intersection. -/
theorem genericClosureSmoothStructure_isPullback :
    IsPullback (genericKernelToClosureSmooth W hΔ i)
      (i ≫ integralCurveStructure (W.map (algebraMap R K)))
      (genericClosureSmoothStructure W i) (Spec.map (CommRingCat.ofHom (algebraMap R K))) := by
  simpa only [Category.id_comp, genericClosureSmoothStructure] using
    (genericKernelToClosureSmooth_isPullback W hΔ i).flip.paste_vert
      (genericKernelClosureStructure_isPullback W i)

/-- The exact original generic kernel, identified with the smooth intersection's generic fiber. -/
def genericClosureSmoothGenericIso : H ≅
    pullback (genericClosureSmoothStructure W i)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  (genericClosureSmoothStructure_isPullback W hΔ i).isoPullback

/-- The generic isomorphism retains the actual map to the smooth intersection. -/
@[reassoc] theorem genericClosureSmoothGenericIso_fst :
    (genericClosureSmoothGenericIso W hΔ i).hom ≫ pullback.fst _ _ =
      genericKernelToClosureSmooth W hΔ i :=
  (genericClosureSmoothStructure_isPullback W hΔ i).isoPullback_hom_fst

/-- The generic isomorphism retains the exact original generic structure map. -/
@[reassoc] theorem genericClosureSmoothGenericIso_snd :
    (genericClosureSmoothGenericIso W hΔ i).hom ≫ pullback.snd _ _ =
      i ≫ integralCurveStructure (W.map (algebraMap R K)) :=
  (genericClosureSmoothStructure_isPullback W hΔ i).isoPullback_hom_snd

end FLT.Mazur.WeierstrassIntegralChart
