/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassFiveRegularChartDescent
public import FLT.Mazur.WeierstrassFlatSectionRegular

/-!
# Five-regular descent using scheme presentations

Convert chart morphisms on an affine spectrum into their actual ring maps.
The resulting associativity criterion takes the global sections supplied by
flat chart and addition projections directly.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R S A : Type u} [CommRing R] [CommRing S] [CommRing A]

/-- The ring map underlying a morphism between two explicit spectra. -/
def affineChartRingHom (f : Spec (.of S) ⟶ Spec (.of A)) : A →+* S :=
  (Scheme.ΓSpecIso (.of S)).hom.hom.comp (specSectionHom f)

/-- Passing to the ring map and back recovers the original chart morphism. -/
theorem affineChartRingHom_spec (f : Spec (.of S) ⟶ Spec (.of A)) :
    Spec.map (CommRingCat.ofHom (affineChartRingHom f)) = f := by
  apply specSectionHom_injective
  unfold specSectionHom affineChartRingHom
  change ((Scheme.ΓSpecIso (.of A)).inv ≫
    (Spec.map ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop ≫
      (Scheme.ΓSpecIso (.of S)).hom)).appTop).hom = _
  rw [← Scheme.ΓSpecIso_inv_naturality]
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The spectrum identification preserves regular elements of global sections. -/
theorem affineChartRingHom_isRegular (f : Spec (.of S) ⟶ Spec (.of A)) {a : A}
    (ha : IsRegular (specSectionHom f a)) : IsRegular (affineChartRingHom f a) :=
  flatRingHom_isRegular (Scheme.ΓSpecIso (.of S)).hom.hom
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _)) ha

variable (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- Five regular chart sections imply associativity on any explicit affine spectrum. -/
theorem integralCurveTripleAdd_of_fiveRegularSections
    (t : Spec (.of S) ⟶ integralCurveTriple W) (j : Fin 5 → Fin 3)
    (p : (i : Fin 5) → Spec (.of S) ⟶ chartScheme W (j i))
    (hp : ∀ i, p i ≫ integralCurveChart W (j i) = tripleFivePoint W hΔ t i)
    (hz : ∀ i, IsRegular (specSectionHom (p i) (coord W (j i) 2))) (c e : Fin 3)
    (l : Spec (.of S) ⟶ chartScheme W c) (r : Spec (.of S) ⟶ chartScheme W e)
    (hl : l ≫ integralCurveChart W c = t ≫ integralCurveTripleAddLeft W hΔ)
    (hr : r ≫ integralCurveChart W e = t ≫ integralCurveTripleAddRight W hΔ) :
    t ≫ integralCurveTripleAddLeft W hΔ = t ≫ integralCurveTripleAddRight W hΔ := by
  apply integralCurveTripleAdd_of_fiveRegularCharts W hΔ t j
    (fun i => affineChartRingHom (p i))
    (fun i => by rw [affineChartRingHom_spec]; exact hp i)
    (fun i => affineChartRingHom_isRegular (p i) (hz i)) c e
    (affineChartRingHom l) (affineChartRingHom r)
  · simpa only [affineChartRingHom_spec] using hl
  · simpa only [affineChartRingHom_spec] using hr

end FLT.Mazur.WeierstrassIntegralChart
