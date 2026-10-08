/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassAffineOutputTripleGlobal

/-!
# Actual open addition domains with affine output

Localize each addition domain at its output z-coordinate. The resulting
principal open maps to the genuine curve product and factors through an
ordinary domain. These constructions supply concrete triple intersections.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

universe u
variable {R : Type u} [CommRing R] (W : WeierstrassCurve R)

/-- The actual principal open where this addition chart has affine output. -/
abbrev AdditionAffineOpenRing (i : AdditionChartIndex) :=
  Localization.Away (additionChartAlgOutput W i (coord W (additionChartOutput i) 2))

/-- Inclusion of the output-affine principal open into its original addition chart. -/
def additionAffineOpenProjection (i : AdditionChartIndex) :
    Spec (.of (AdditionAffineOpenRing W i)) ⟶ Spec (additionChartRing W i) :=
  Spec.map (CommRingCat.ofHom (algebraMap (additionChartRing W i) (AdditionAffineOpenRing W i)))

instance additionAffineOpenProjection_isOpenImmersion (i : AdditionChartIndex) :
    IsOpenImmersion (additionAffineOpenProjection W i) := by
  unfold additionAffineOpenProjection
  infer_instance

/-- The affine-output open carries its original global pair of inputs. -/
def additionAffineOpenDomain (i : AdditionChartIndex) :
    Spec (.of (AdditionAffineOpenRing W i)) ⟶ integralCurveProduct W :=
  additionAffineOpenProjection W i ≫ additionGlobalDomain W i

instance additionAffineOpenDomain_isOpenImmersion (i : AdditionChartIndex) :
    IsOpenImmersion (additionAffineOpenDomain W i) := by
  unfold additionAffineOpenDomain
  infer_instance

/-- The affine-output condition holds after every scheme map to this principal open. -/
theorem additionAffineOpenProjection_unit {X : Scheme.{u}} (i : AdditionChartIndex)
    (f : X ⟶ Spec (.of (AdditionAffineOpenRing W i))) :
    IsUnit (specSectionHom (f ≫ additionAffineOpenProjection W i)
      (additionChartAlgOutput W i (coord W (additionChartOutput i) 2))) := by
  rw [additionAffineOpenProjection.eq_def, specSectionHom_comp]
  exact (IsLocalization.Away.algebraMap_isUnit
    (additionChartAlgOutput W i (coord W (additionChartOutput i) 2))
    (S := AdditionAffineOpenRing W i)).map (specSectionHom f)

/-- This principal open has a canonical ordinary-domain factorization. -/
def additionAffineOpenOrdinary (i : AdditionChartIndex) :
    Spec (.of (AdditionAffineOpenRing W i)) ⟶
      Spec (additionChartRing W (ordinaryIndex (additionOrdinaryChoice i))) :=
  additionAffineOutputScheme W i (additionAffineOpenProjection W i)
    (by simpa only [Category.id_comp] using additionAffineOpenProjection_unit W i (𝟙 _))

/-- The ordinary factorization has exactly the original global input pair. -/
theorem additionAffineOpenOrdinary_inputs (i : AdditionChartIndex) :
    additionAffineOpenOrdinary W i ≫ ordinaryGlobalDomain W (additionOrdinaryChoice i) =
      additionAffineOpenDomain W i :=
  additionAffineOutputScheme_inputs W i _ _

/-- Every compatible common scheme in four affine-output opens satisfies associativity. -/
theorem integralCurveTripleAdd_affineOpen (hΔ : IsUnit W.Δ) {X : Scheme.{u}}
    (t : X ⟶ integralCurveTriple W) (i j k l : AdditionChartIndex)
    (f : X ⟶ Spec (.of (AdditionAffineOpenRing W i)))
    (g : X ⟶ Spec (.of (AdditionAffineOpenRing W j)))
    (h : X ⟶ Spec (.of (AdditionAffineOpenRing W k)))
    (q : X ⟶ Spec (.of (AdditionAffineOpenRing W l)))
    (hf : f ≫ additionAffineOpenDomain W i = t ≫ integralCurveTriplePair W)
    (hg : g ≫ additionAffineOpenDomain W j = t ≫ integralCurveTripleLastPair W)
    (hh : h ≫ additionAffineOpenDomain W k = t ≫ integralCurveAddFirstPair W hΔ)
    (hq : q ≫ additionAffineOpenDomain W l = t ≫ integralCurveAddLastPair W hΔ) :
    t ≫ integralCurveTripleAddLeft W hΔ = t ≫ integralCurveTripleAddRight W hΔ := by
  apply integralCurveTripleAdd_allOrdinary W hΔ t
    (additionOrdinaryChoice i) (additionOrdinaryChoice j)
    (additionOrdinaryChoice k) (additionOrdinaryChoice l)
    (f ≫ additionAffineOpenOrdinary W i) (g ≫ additionAffineOpenOrdinary W j)
    (h ≫ additionAffineOpenOrdinary W k) (q ≫ additionAffineOpenOrdinary W l)
  · simpa only [Category.assoc, additionAffineOpenOrdinary_inputs] using hf
  · simpa only [Category.assoc, additionAffineOpenOrdinary_inputs] using hg
  · simpa only [Category.assoc, additionAffineOpenOrdinary_inputs] using hh
  · simpa only [Category.assoc, additionAffineOpenOrdinary_inputs] using hq

end FLT.Mazur.WeierstrassIntegralChart
