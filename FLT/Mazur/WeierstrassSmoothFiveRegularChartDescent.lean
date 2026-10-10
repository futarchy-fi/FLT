/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSmoothFivePoints
public import FLT.Mazur.WeierstrassChartInjectiveDescent

/-!
# Five regular coordinates with arbitrary output charts

Localizing the five input and intermediate coordinates makes all five points
affine. Cross-coordinate descent reflects the resulting associativity identity
even when the two final outputs use different projective charts.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- Five regular coordinates suffice for arbitrary final chart presentations. -/
theorem smoothFactorTripleAdd_of_fiveRegularCharts {S : Type u} [CommRing S]
    (t : Spec (.of S) ⟶ smoothFactorTriple W) (j : Fin 5 → Fin 3)
    (p : (i : Fin 5) → Coordinate W (j i) →+* S)
    (hp : ∀ i, Spec.map (CommRingCat.ofHom (p i)) ≫ integralCurveChart W (j i) =
      smoothTripleFivePoint W t i)
    (hz : ∀ i, IsRegular (p i (coord W (j i) 2))) (c e : Fin 3)
    (l : Coordinate W c →+* S) (r : Coordinate W e →+* S)
    (hl : Spec.map (CommRingCat.ofHom l) ≫ integralCurveChart W c =
      t ≫ smoothFactorTripleAddLeft W ≫ (integralSmoothOpen W).ι)
    (hr : Spec.map (CommRingCat.ofHom r) ≫ integralCurveChart W e =
      t ≫ smoothFactorTripleAddRight W ≫ (integralSmoothOpen W).ι) :
    t ≫ smoothFactorTripleAddLeft W = t ≫ smoothFactorTripleAddRight W := by
  let d : S := ∏ i, p i (coord W (j i) 2)
  let T := Localization.Away d
  let a : S →+* T := algebraMap S T
  let f : Spec (.of T) ⟶ Spec (.of S) := Spec.map (CommRingCat.ofHom a)
  have hd : IsRegular d := IsRegular.prod (fun i _ => hz i)
  have hi : Function.Injective a := by
    apply IsLocalization.injective T (M := Submonoid.powers d)
    rintro x ⟨n, rfl⟩
    exact (hd.pow n).mem_nonZeroDivisors
  have hu (i : Fin 5) : IsUnit (a (p i (coord W (j i) 2))) := by
    apply isUnit_of_dvd_unit (map_dvd a (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
    exact IsLocalization.Away.algebraMap_isUnit d
  have ha (i : Fin 5) : ∃ q : Spec (.of T) ⟶ chartScheme W 2,
      q ≫ integralCurveChart W 2 = smoothTripleFivePoint W (f ≫ t) i := by
    obtain ⟨q, hq⟩ := exists_chart_of_coordinate_unit W (j i) 2
      (f ≫ Spec.map (CommRingCat.ofHom (p i))) (by
        rw [specSectionHom_comp]
        change IsUnit (specSectionHom (Spec.map (CommRingCat.ofHom a))
          (p i (coord W (j i) 2)))
        rw [show Spec.map (CommRingCat.ofHom a) =
          𝟙 _ ≫ Spec.map (CommRingCat.ofHom a) from (Category.id_comp _).symm,
          specSectionHom_comp]
        exact (hu i).map (specSectionHom (𝟙 _)))
    exact ⟨q, hq.trans (by rw [Category.assoc, hp, smoothTripleFivePoint_comp])⟩
  choose q hq using ha
  have he := smoothFactorTripleAdd_of_fiveAffine W (f ≫ t)
    (q 0) (q 1) (q 2) (q 3) (q 4) (hq 0) (hq 1) (hq 2) (hq 3) (hq 4)
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  rw [Category.assoc, Category.assoc, ← hl, ← hr]
  apply chart_global_eq_of_ring_injective W a hi c e
  have he' := congrArg (fun g => g ≫ (integralSmoothOpen W).ι) he
  simpa only [Category.assoc, hl, hr] using he'

end FLT.Mazur.WeierstrassIntegralChart
