/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassChartUnitLift
public import FLT.Mazur.WeierstrassFiveAffineTriple
public import Mathlib.Algebra.Regular.Pow

/-!
# Mixed-chart associativity from five regular coordinates

For an affine source, the three inputs and both intermediate sums may use
arbitrary projective charts. If their five Z coordinates are regular, invert
their product and use the five-affine theorem. Injectivity of this localization
then proves equality when the final outputs have a common chart presentation.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R) (hΔ : IsUnit W.Δ)

/-- The three actual original inputs followed by the two actual inner sums. -/
def tripleFivePoint {X : Scheme.{u}} (t : X ⟶ integralCurveTriple W) :
    Fin 5 → (X ⟶ integralCurve W) :=
  ![t ≫ integralCurveTripleFirst W, t ≫ integralCurveTripleSecond W,
    t ≫ integralCurveTripleThird W,
    t ≫ integralCurveTriplePair W ≫ integralCurveAddition W hΔ,
    t ≫ integralCurveTripleLastPair W ≫ integralCurveAddition W hΔ]

/-- The five selected points commute with changing the source. -/
theorem tripleFivePoint_comp {X Y : Scheme.{u}} (t : X ⟶ integralCurveTriple W)
    (f : Y ⟶ X) (i : Fin 5) :
    tripleFivePoint W hΔ (f ≫ t) i = f ≫ tripleFivePoint W hΔ t i := by
  fin_cases i <;> simp [tripleFivePoint, Category.assoc]

/-- Mixed input charts suffice if their five Z coordinates are regular and outputs share a chart. -/
theorem integralCurveTripleAdd_of_fiveRegular {S : Type u} [CommRing S]
    (t : Spec (.of S) ⟶ integralCurveTriple W) (j : Fin 5 → Fin 3)
    (p : (i : Fin 5) → Coordinate W (j i) →+* S)
    (hp : ∀ i, Spec.map (CommRingCat.ofHom (p i)) ≫ integralCurveChart W (j i) =
      tripleFivePoint W hΔ t i)
    (hz : ∀ i, IsRegular (p i (coord W (j i) 2))) (c : Fin 3)
    (l r : Coordinate W c →+* S)
    (hl : Spec.map (CommRingCat.ofHom l) ≫ integralCurveChart W c =
      t ≫ integralCurveTripleAddLeft W hΔ)
    (hr : Spec.map (CommRingCat.ofHom r) ≫ integralCurveChart W c =
      t ≫ integralCurveTripleAddRight W hΔ) :
    t ≫ integralCurveTripleAddLeft W hΔ = t ≫ integralCurveTripleAddRight W hΔ := by
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
      q ≫ integralCurveChart W 2 = tripleFivePoint W hΔ (f ≫ t) i := by
    obtain ⟨q, hq⟩ := exists_chart_of_coordinate_unit W (j i) 2
      (f ≫ Spec.map (CommRingCat.ofHom (p i))) (by
        rw [specSectionHom_comp]
        change IsUnit (specSectionHom (Spec.map (CommRingCat.ofHom a))
          (p i (coord W (j i) 2)))
        rw [show Spec.map (CommRingCat.ofHom a) =
          𝟙 _ ≫ Spec.map (CommRingCat.ofHom a) from (Category.id_comp _).symm,
          specSectionHom_comp]
        exact (hu i).map (specSectionHom (𝟙 _)))
    exact ⟨q, hq.trans (by rw [Category.assoc, hp, tripleFivePoint_comp])⟩
  choose q hq using ha
  have he := integralCurveTripleAdd_of_fiveAffine W hΔ (f ≫ t)
    (q 0) (q 1) (q 2) (q 3) (q 4) (hq 0) (hq 1) (hq 2) (hq 3) (hq 4)
  have he' : f ≫ Spec.map (CommRingCat.ofHom l) =
      f ≫ Spec.map (CommRingCat.ofHom r) := by
    apply (cancel_mono (integralCurveChart W c)).mp
    simpa only [Category.assoc, hl, hr] using he
  have hlr : l = r := by
    apply RingHom.ext
    intro x
    apply hi
    have hmaps : a.comp l = a.comp r := by
      have hs : Spec.map (CommRingCat.ofHom (a.comp l)) =
          Spec.map (CommRingCat.ofHom (a.comp r)) := by
        simpa only [CommRingCat.ofHom_comp, Spec.map_comp] using he'
      exact congrArg CommRingCat.Hom.hom (Spec.map_injective hs)
    exact DFunLike.congr_fun hmaps x
  rw [← hl, ← hr, hlr]

end FLT.Mazur.WeierstrassIntegralChart
