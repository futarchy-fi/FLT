/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertChartIdealEvaluation
public import FLT.Mazur.AffineIdealSheafComparison

/-!
# Actual ideal-sheaf comparison across Hilbert chart transitions

Two ambient maps lying over the same transition and the same original
polynomial-space map pull back the universal chart ideals to equal ideal
sheaves. The test scheme is arbitrary.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry
open FLT.Mazur.BaseAdicThickening

universe u

namespace FLT.Mazur.HilbertChart

set_option backward.isDefEq.respectTransparency false

variable (R : Type u) [CommRing R] (I : Type u) (d : ℕ)
variable (w v : Fin d → MvPolynomial I R)

/-- Cache the coefficient ring for ambient ideal inference. -/
local instance sheafTransitionCoefficientsRing : CommRing (Coefficients R I d) := inferInstance
/-- Cache the source chart ring for ambient ideal inference. -/
local instance sheafTransitionSourceRing : CommRing (ChartRing R I d w) := inferInstance
/-- Cache the target chart ring for ambient ideal inference. -/
local instance sheafTransitionTargetRing : CommRing (ChartRing R I d v) := inferInstance

/-- The actual ideal sheaf of the universal chart ideal in polynomial coordinates. -/
def chartPolynomialIdealSheaf :
    (Spec (.of (MvPolynomial I (ChartRing R I d w)))).IdealSheafData :=
  baseIdeal _ (chartIdentityIdeal R I d w)

/-- Projection of the polynomial ambient scheme to its Hilbert chart. -/
def chartPolynomialProjection : Spec (.of (MvPolynomial I (ChartRing R I d w))) ⟶
    Spec (.of (ChartRing R I d w)) := Spec.map (CommRingCat.ofHom MvPolynomial.C)

/-- The polynomial ambient scheme maps to the original polynomial space over `R`. -/
def chartPolynomialOriginal : Spec (.of (MvPolynomial I (ChartRing R I d w))) ⟶
    Spec (.of (MvPolynomial I R)) :=
  Spec.map (CommRingCat.ofHom (MvPolynomial.map (algebraMap R (ChartRing R I d w))))

/-- The ideal-sheaf comparison on affine ambient tests retains the entire ideal. -/
theorem chartPolynomialIdealSheaf_affineTransition {S : Type u} [CommRing S]
    (F : MvPolynomial I (ChartRing R I d w) →+* S)
    (G : MvPolynomial I (ChartRing R I d v) →+* S)
    (g : Spec (.of S) ⟶ (chartTupleTransitionOpen R I d w v).toScheme)
    (hF : g ≫ (chartTupleTransitionOpen R I d w v).ι =
      Spec.map (CommRingCat.ofHom (F.comp MvPolynomial.C)))
    (hG : g ≫ chartTupleTransition R I d w v =
      Spec.map (CommRingCat.ofHom (G.comp MvPolynomial.C)))
    (hX : ∀ i, F (MvPolynomial.X i) = G (MvPolynomial.X i)) :
    (chartPolynomialIdealSheaf R I d w).comap (Spec.map (CommRingCat.ofHom F)) =
      (chartPolynomialIdealSheaf R I d v).comap (Spec.map (CommRingCat.ofHom G)) := by
  rw [chartPolynomialIdealSheaf, chartPolynomialIdealSheaf,
    baseIdeal_comap_specMap, baseIdeal_comap_specMap]
  exact congrArg (baseIdeal (.of S))
    (chartIdentityIdeal_transition_evaluation R I d w v F G g hF hG hX)

/-- Universal chart ideals agree on every scheme test of an ambient transition. -/
theorem chartPolynomialIdealSheaf_transition {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d w))))
    (g : X ⟶ Spec (.of (MvPolynomial I (ChartRing R I d v))))
    (k : X ⟶ (chartTupleTransitionOpen R I d w v).toScheme)
    (hf : k ≫ (chartTupleTransitionOpen R I d w v).ι =
      f ≫ chartPolynomialProjection R I d w)
    (hg : k ≫ chartTupleTransition R I d w v = g ≫ chartPolynomialProjection R I d v)
    (hp : f ≫ chartPolynomialOriginal R I d w = g ≫ chartPolynomialOriginal R I d v) :
    (chartPolynomialIdealSheaf R I d w).comap f =
      (chartPolynomialIdealSheaf R I d v).comap g := by
  apply idealSheaf_ext_of_affineTests
  intro A a
  let F := (Spec.preimage (a ≫ f)).hom
  let G := (Spec.preimage (a ≫ g)).hom
  have hF : Spec.map (CommRingCat.ofHom F) = a ≫ f := Spec.map_preimage _
  have hG : Spec.map (CommRingCat.ofHom G) = a ≫ g := Spec.map_preimage _
  rw [← Scheme.IdealSheafData.comap_comp, ← Scheme.IdealSheafData.comap_comp, ← hF, ← hG]
  apply chartPolynomialIdealSheaf_affineTransition R I d w v F G (a ≫ k)
  · rw [CommRingCat.ofHom_comp, Spec.map_comp, hF]
    simpa only [Category.assoc, chartPolynomialProjection] using congrArg (a ≫ ·) hf
  · rw [CommRingCat.ofHom_comp, Spec.map_comp, hG]
    simpa only [Category.assoc, chartPolynomialProjection] using congrArg (a ≫ ·) hg
  · have he : F.comp (MvPolynomial.map (algebraMap R (ChartRing R I d w))) =
        G.comp (MvPolynomial.map (algebraMap R (ChartRing R I d v))) := by
      suffices e : Spec.map (CommRingCat.ofHom
          (F.comp (MvPolynomial.map (algebraMap R (ChartRing R I d w))))) =
          Spec.map (CommRingCat.ofHom
            (G.comp (MvPolynomial.map (algebraMap R (ChartRing R I d v))))) by
        exact congrArg CommRingCat.Hom.hom (Spec.map_injective e)
      simp only [CommRingCat.ofHom_comp, Spec.map_comp, hF, hG, Category.assoc]
      exact congrArg (a ≫ ·) hp
    intro i
    simpa using DFunLike.congr_fun he (MvPolynomial.X i)

end FLT.Mazur.HilbertChart
