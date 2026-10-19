/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedGenericCurve

/-!
# The original kernel closure in the full divided model

Take the schematic image of the exact original generic kernel in the concrete
proper divided model. Its generic fiber recovers the original inclusion and
structure map. This construction does not discard points over singular reduction.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassIntegralChart
set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [IsDomain R] [IsBezout R]
  [Field K] [Algebra R K] [IsFractionRing R K]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val)) (j : ℕ) (hj : j ≤ n)
  (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]

/-- The original generic kernel mapped into the full concrete divided model. -/
def finiteGlobalGenericKernel : H ⟶ finiteGlobalModel hπ data j hj :=
  i ≫ finiteGlobalGenericCurve hπ data j hj hΔ

instance finiteGlobalGenericKernel_quasiCompact :
    QuasiCompact (finiteGlobalGenericKernel hπ data j hj hΔ i) :=
  inferInstanceAs (QuasiCompact (i ≫ finiteGlobalGenericCurve hπ data j hj hΔ))

/-- The full schematic kernel closure, including all special-fiber points. -/
def finiteGlobalKernelClosure : Scheme := (finiteGlobalGenericKernel hπ data j hj hΔ i).image

/-- Its actual closed embedding in the proper divided model. -/
def finiteGlobalKernelClosureInclusion : finiteGlobalKernelClosure hπ data j hj hΔ i ⟶
    finiteGlobalModel hπ data j hj := (finiteGlobalGenericKernel hπ data j hj hΔ i).imageι

/-- The same original generic source factors through its constructed divided closure. -/
def finiteGlobalKernelToClosure : H ⟶ finiteGlobalKernelClosure hπ data j hj hΔ i :=
  (finiteGlobalGenericKernel hπ data j hj hΔ i).toImage

omit [IsFractionRing R K] [IsClosedImmersion i] in
/-- The closure retains the actual original generic inclusion in the divided model. -/
@[reassoc] theorem finiteGlobalKernelToClosure_inclusion :
    finiteGlobalKernelToClosure hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureInclusion hπ data j hj hΔ i =
        i ≫ finiteGlobalGenericCurve hπ data j hj hΔ :=
  (finiteGlobalGenericKernel hπ data j hj hΔ i).toImage_imageι

instance finiteGlobalKernelClosureInclusion_closed :
    IsClosedImmersion (finiteGlobalKernelClosureInclusion hπ data j hj hΔ i) :=
  inferInstanceAs (IsClosedImmersion (finiteGlobalGenericKernel hπ data j hj hΔ i).imageι)

instance finiteGlobalKernelToClosure_dense :
    IsSchemeTheoreticallyDominant (finiteGlobalKernelToClosure hπ data j hj hΔ i) :=
  Chow.toImage_schemeTheoreticallyDominant (finiteGlobalGenericKernel hπ data j hj hΔ i)

instance finiteGlobalKernelToClosure_quasiCompact :
    QuasiCompact (finiteGlobalKernelToClosure hπ data j hj hΔ i) :=
  inferInstanceAs (QuasiCompact (finiteGlobalGenericKernel hπ data j hj hΔ i).toImage)

/-- The divided closure keeps the original integral coefficient base. -/
def finiteGlobalKernelClosureStructure :
    finiteGlobalKernelClosure hπ data j hj hΔ i ⟶ Spec (.of R) :=
  finiteGlobalKernelClosureInclusion hπ data j hj hΔ i ≫ finiteGlobalStructure hπ data j hj

instance finiteGlobalKernelClosureStructure_proper :
    IsProper (finiteGlobalKernelClosureStructure hπ data j hj hΔ i) :=
  inferInstanceAs (IsProper (finiteGlobalKernelClosureInclusion hπ data j hj hΔ i ≫
    finiteGlobalStructure hπ data j hj))

/-- The exact generic closed inclusion is recovered, with all its scheme structure. -/
theorem finiteGlobalKernelClosureInclusion_isPullback :
    IsPullback (finiteGlobalKernelToClosure hπ data j hj hΔ i) i
      (finiteGlobalKernelClosureInclusion hπ data j hj hΔ i)
      (finiteGlobalGenericCurve hπ data j hj hΔ) :=
  FlatMonoSchematicClosure.closure_isPullback i (finiteGlobalGenericCurve hπ data j hj hΔ)

/-- The original kernel is the whole generic fiber of its divided closure. -/
theorem finiteGlobalKernelClosureStructure_isPullback :
    IsPullback (finiteGlobalKernelToClosure hπ data j hj hΔ i)
      (i ≫ integralCurveStructure (W.map (algebraMap R K)))
      (finiteGlobalKernelClosureStructure hπ data j hj hΔ i)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  (finiteGlobalKernelClosureInclusion_isPullback hπ data j hj hΔ i).paste_vert
    (finiteGlobalGenericCurve_isPullback hπ data j hj hΔ)

/-- Retain the original generic structure map under the actual closure inclusion. -/
@[reassoc] theorem finiteGlobalKernelToClosure_structure :
    finiteGlobalKernelToClosure hπ data j hj hΔ i ≫
      finiteGlobalKernelClosureStructure hπ data j hj hΔ i =
        (i ≫ integralCurveStructure (W.map (algebraMap R K))) ≫
          Spec.map (CommRingCat.ofHom (algebraMap R K)) :=
  (finiteGlobalKernelClosureStructure_isPullback hπ data j hj hΔ i).w

/-- Constructed generic comparison for the full divided closure. -/
def finiteGlobalKernelClosureGenericIso : H ≅
    pullback (finiteGlobalKernelClosureStructure hπ data j hj hΔ i)
      (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
  (finiteGlobalKernelClosureStructure_isPullback hπ data j hj hΔ i).isoPullback

/-- The comparison retains the exact map from the original generic kernel. -/
@[reassoc] theorem finiteGlobalKernelClosureGenericIso_fst :
    (finiteGlobalKernelClosureGenericIso hπ data j hj hΔ i).hom ≫ pullback.fst _ _ =
      finiteGlobalKernelToClosure hπ data j hj hΔ i :=
  (finiteGlobalKernelClosureStructure_isPullback hπ data j hj hΔ i).isoPullback_hom_fst

/-- The comparison retains the exact original generic structure morphism. -/
@[reassoc] theorem finiteGlobalKernelClosureGenericIso_snd :
    (finiteGlobalKernelClosureGenericIso hπ data j hj hΔ i).hom ≫ pullback.snd _ _ =
      i ≫ integralCurveStructure (W.map (algebraMap R K)) :=
  (finiteGlobalKernelClosureStructure_isPullback hπ data j hj hΔ i).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
