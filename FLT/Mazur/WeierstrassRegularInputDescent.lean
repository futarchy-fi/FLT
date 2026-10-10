/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassFiveRegularSectionDescent

/-!
# Injective descent after making finitely many inputs affine

Regular normalized Z coordinates give an injective localization. Equality
of two chart-presented outputs can therefore be checked with all inputs affine.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S : Type u} [CommRing R] [CommRing S] (W : WeierstrassCurve R)

/-- Finitely many regular input coordinates detect equality of arbitrary output charts. -/
theorem chart_outputs_eq_of_regular_inputs (n : ℕ) (j : Fin n → Fin 3)
    (p : (i : Fin n) → Spec (.of S) ⟶ chartScheme W (j i))
    (hz : ∀ i, IsRegular (specSectionHom (p i) (coord W (j i) 2))) (c e : Fin 3)
    (l : Spec (.of S) ⟶ chartScheme W c) (r : Spec (.of S) ⟶ chartScheme W e)
    (h : ∀ (T : Type u) [CommRing T] (f : Spec (.of T) ⟶ Spec (.of S))
      (q : Fin n → (Spec (.of T) ⟶ chartScheme W 2)),
      (∀ i, q i ≫ integralCurveChart W 2 = f ≫ p i ≫ integralCurveChart W (j i)) →
      f ≫ l ≫ integralCurveChart W c = f ≫ r ≫ integralCurveChart W e) :
    l ≫ integralCurveChart W c = r ≫ integralCurveChart W e := by
  let z (i : Fin n) : S := affineChartRingHom (p i) (coord W (j i) 2)
  let d : S := ∏ i, z i
  let T := Localization.Away d
  let a : S →+* T := algebraMap S T
  let f : Spec (.of T) ⟶ Spec (.of S) := Spec.map (CommRingCat.ofHom a)
  have hd : IsRegular d := IsRegular.prod
    (fun i _ => affineChartRingHom_isRegular (p i) (hz i))
  have hi : Function.Injective a := by
    apply IsLocalization.injective T (M := Submonoid.powers d)
    rintro x ⟨m, rfl⟩
    exact (hd.pow m).mem_nonZeroDivisors
  have hu (i : Fin n) : IsUnit (a (z i)) := by
    apply isUnit_of_dvd_unit (map_dvd a (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)))
    exact IsLocalization.Away.algebraMap_isUnit d
  have ha (i : Fin n) : ∃ q : Spec (.of T) ⟶ chartScheme W 2,
      q ≫ integralCurveChart W 2 = f ≫ p i ≫ integralCurveChart W (j i) := by
    obtain ⟨q, hq⟩ := exists_chart_of_coordinate_unit W (j i) 2 (f ≫ p i) (by
      rw [← affineChartRingHom_spec (p i), specSectionHom_comp]
      change IsUnit (specSectionHom (Spec.map (CommRingCat.ofHom a)) (z i))
      rw [show Spec.map (CommRingCat.ofHom a) =
        𝟙 _ ≫ Spec.map (CommRingCat.ofHom a) from (Category.id_comp _).symm,
        specSectionHom_comp]
      exact (hu i).map (specSectionHom (𝟙 _)))
    exact ⟨q, hq.trans (Category.assoc _ _ _)⟩
  choose q hq using ha
  exact chart_global_eq_of_ring_injective W a hi c e l r (h T f q hq)

end FLT.Mazur.WeierstrassIntegralChart
