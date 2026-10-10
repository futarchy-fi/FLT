/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ProjectiveLineScaledReciprocalGluing
public import FLT.Mazur.ProjectiveLineChartIntersection

/-!
# Pointwise injectivity from the original projective affine charts

Injective affine pieces and their exact Laurent intersection prevent any extra
identifications after gluing. Parameter isomorphisms and signed scales are retained.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.ProjectiveLine
universe u
variable {K : Type u} [Field K] {X A : Scheme.{u}}

/-- It suffices to check both affine pieces and their cross-chart identifications. -/
theorem map_injective_of_charts (f : scheme K ⟶ X)
    (hl : Function.Injective (left K ≫ f))
    (hr : Function.Injective (right K ≫ f))
    (hc : ∀ x y, (left K ≫ f) x = (right K ≫ f) y → left K x = right K y) :
    Function.Injective f := by
  intro x y hxy
  rcases charts_cover K x with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;>
    rcases charts_cover K y with ⟨w, rfl⟩ | ⟨w, rfl⟩
  · exact congrArg (left K) (hl hxy)
  · exact hc v w hxy
  · exact (hc w v hxy.symm).symm
  · exact congrArg (right K) (hr hxy)

/-- A parameter pullback with the original puncture proves injectivity of the full map. -/
theorem map_injective_of_parameter_pullback (f : scheme K ⟶ X)
    (e : chart K ≅ A) (v : chart K ⟶ chart K) (p : A ⟶ X) (g : chart K ⟶ X)
    (hv : Function.Injective v) (hp : Function.Injective p) (hg : Function.Injective g)
    (hl : left K ≫ f = e.hom ≫ p) (hr : right K ≫ f = v ≫ g)
    (H : IsPullback (overlapRight K ≫ v) (overlapLeft K ≫ e.hom) g p) :
    Function.Injective f := by
  apply map_injective_of_charts f
  · rw [hl]
    exact hp.comp e.hom.homeomorph.injective
  · rw [hr]
    exact hg.comp hv
  · intro x y hxy
    rw [hl, hr] at hxy
    obtain ⟨z, hz, hx⟩ := Scheme.exists_preimage_of_isPullback H (v y) (e.hom x) hxy.symm
    have hzx : overlapLeft K z = x := e.hom.homeomorph.injective hx
    have hzy : overlapRight K z = y := hv hz
    rw [← hzx, ← hzy]
    exact congrArg (fun m : overlap K ⟶ scheme K => m z) (overlap_condition K)

/-- Affine scaling by a unit is injective on every scheme point. -/
theorem chartScaling_injective (a : Kˣ) : Function.Injective (chartScaling K a) := by
  intro x y hxy
  have H := congrArg (chartScaling K a⁻¹) hxy
  change (chartScaling K a ≫ chartScaling K a⁻¹) x =
    (chartScaling K a ≫ chartScaling K a⁻¹) y at H
  rw [← chartScaling_mul, mul_inv_cancel, chartScaling_one] at H
  exact H

end FLT.Mazur.ProjectiveLine
