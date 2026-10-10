/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IncreasingCechCoefficientDifferential
public import FLT.Mazur.IncreasingCechCartesianReindex

/-!
# Reindexing actual cartesian chart sections

Finite intersections commute with inverse image. Restriction along this equality
identifies the cartesian chart complex with the bounded complex on the actual
inverse-image cover.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.IncreasingCechCoefficients
open Scheme.Modules hiding map_smul
open IncreasingCechCartesian (preimage_tuple equalOpenSections equalOpenSections_apply)
open IncreasingCechComplex IncreasingCechScalars FCurve Chow CechSheafHZero

variable {P X T : Scheme.{0}} (p : P ⟶ X) (q : P ⟶ T) (M : X.Modules)
  {ι : Type} [LinearOrder ι] (U : ι → X.Opens)

/-- Cartesian chart coordinates give the actual bounded term of the inverse-image cover. -/
def chartTermEquiv (n : ℕ) :
    ChartTerm (p := p) (q := q) M U n ≃ₗ[Γ(T, ⊤)]
      BaseTerm ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n :=
  (LinearEquiv.piCongrRight fun a ↦
    equalOpenSections ((pullback p).obj M) q.appTop.hom (preimage_tuple p U n a)).trans
      (baseTermCoordinates ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n).symm

/-- The reindexing map uses actual restrictions along equal tuple opens. -/
lemma chartTermEquiv_apply (n : ℕ) (x : ChartTerm (p := p) (q := q) M U n)
    (a : Tuple (ι := ι) n) :
    baseTermCoordinates ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n
      (chartTermEquiv p q M U n x) a =
        baseRestriction ((pullback p).obj M) q.appTop.hom (preimage_tuple p U n a).ge (x a) :=
  equalOpenSections_apply _ _ _ _

/-- Reindexing preserves the signed actual restriction differential. -/
lemma chartTermEquiv_d (n : ℕ) (x : ChartTerm (p := p) (q := q) M U n) :
    chartTermEquiv p q M U (n + 1) (chartD M U n x) =
      baseD ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i) q.appTop.hom n
        (chartTermEquiv p q M U n x) := by
  apply (baseTermCoordinates ((pullback p).obj M) (fun i ↦ p ⁻¹ᵁ U i)
    q.appTop.hom (n + 1)).injective
  funext a
  rw [chartTermEquiv_apply, chartD_apply, map_sum, baseD_coordinates]
  apply Finset.sum_congr rfl
  intro k _
  rw [map_zsmul, chartTermEquiv_apply]
  congr 1
  change ((baseRestriction ((pullback p).obj M) q.appTop.hom _).comp
    (baseRestriction ((pullback p).obj M) q.appTop.hom _)) _ =
      ((baseRestriction ((pullback p).obj M) q.appTop.hom _).comp
        (baseRestriction ((pullback p).obj M) q.appTop.hom _)) _
  rw [baseRestriction_comp, baseRestriction_comp]
  rfl

end FLT.Mazur.IncreasingCechCoefficients
