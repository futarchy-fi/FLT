/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.MonoBaseProductComparison
public import FLT.Mazur.WeierstrassValuationClosureSmoothFlat

/-!
# The original generic kernel pairs over the two coefficient bases

The generic source used for dense descent is exactly the original generic
fiber product. The comparison retains both original projections.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false

variable {R K : Type} [CommRing R] [Field K] [Algebra R K] [IsFractionRing R K]
  (W : WeierstrassCurve R) (hΔ : IsUnit (W.map (algebraMap R K)).Δ)
  {H : Scheme} (i : H ⟶ integralCurve (W.map (algebraMap R K))) [IsClosedImmersion i]

local notation "s" => i ≫ integralCurveStructure (W.map (algebraMap R K))
local notation "t" => genericKernelToClosureSmooth W hΔ i ≫ genericClosureSmoothStructure W i

/-- The product over the integral base is the exact original generic product. -/
def genericClosureSmoothPairIso : pullback t t ≅ pullback s s := by
  let _ : Epi (CommRingCat.ofHom (algebraMap R K)) :=
    IsLocalization.epi (nonZeroDivisors R) K
  let hm : Mono (CommRingCat.ofHom (algebraMap R K)).op := inferInstance
  let _ : Mono (Spec.map (CommRingCat.ofHom (algebraMap R K))) :=
    (Functor.mono_map_iff_mono Scheme.Spec _).mpr hm
  exact pullback.congrHom (genericClosureSmoothStructure_isPullback W hΔ i).w
    (genericClosureSmoothStructure_isPullback W hΔ i).w ≪≫
      MonoBaseProductComparison.iso s s (Spec.map (CommRingCat.ofHom (algebraMap R K)))

/-- The comparison retains the original first generic input. -/
@[reassoc] theorem genericClosureSmoothPairIso_fst :
    (genericClosureSmoothPairIso W hΔ i).hom ≫ pullback.fst s s = pullback.fst t t := by
  simp only [genericClosureSmoothPairIso, Iso.trans_hom, Category.assoc,
    MonoBaseProductComparison.iso_hom_fst, pullback.congrHom_hom, pullback.map, pullback.lift_fst,
    Category.comp_id]

/-- The comparison retains the original second generic input. -/
@[reassoc] theorem genericClosureSmoothPairIso_snd :
    (genericClosureSmoothPairIso W hΔ i).hom ≫ pullback.snd s s = pullback.snd t t := by
  simp only [genericClosureSmoothPairIso, Iso.trans_hom, Category.assoc,
    MonoBaseProductComparison.iso_hom_snd, pullback.congrHom_hom, pullback.map, pullback.lift_snd,
    Category.comp_id]

end FLT.Mazur.WeierstrassIntegralChart
