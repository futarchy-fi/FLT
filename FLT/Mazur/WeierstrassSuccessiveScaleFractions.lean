/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDilatationRefinement
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Fractions for the successive scale chart

Dividing both preceding coordinates by π gives the deeper divided equation,
whose cubic coefficient is s*π. The substitution retains the actual refinement.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveScale

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
local notation "B" =>
  WeierstrassDilatation.Coordinate W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BX" => WeierstrassDilatation.x W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "BY" => WeierstrassDilatation.y W s (π * b3) (π * b4) (π ^ 2 * b6)
local notation "D" => WeierstrassDilatation.Coordinate W (s * π) b3 b4 b6
local notation "DX" => WeierstrassDilatation.x W (s * π) b3 b4 b6
local notation "DY" => WeierstrassDilatation.y W (s * π) b3 b4 b6
local notation "ref" => WeierstrassDilatation.refinement W s π
  (π * b3) (π * b4) (π ^ 2 * b6) b3 b4 b6 rfl rfl rfl

/-- Fractions solve the deeper equation without assuming invertibility of the old scale. -/
theorem fraction_equation (f : B →ₐ[R] S) (d : S) (hd : algebraMap R S π * d = 1) :
    (d * f BY) ^ 2 +
        (algebraMap R S W.a₁ * (d * f BX) + algebraMap R S b3) * (d * f BY) =
      algebraMap R S (s * π) * (d * f BX) ^ 3 +
        algebraMap R S W.a₂ * (d * f BX) ^ 2 +
        algebraMap R S b4 * (d * f BX) + algebraMap R S b6 := by
  have hx : algebraMap R S π * (d * f BX) = f BX := by
    rw [← mul_assoc, hd, one_mul]
  have hy : algebraMap R S π * (d * f BY) = f BY := by
    rw [← mul_assoc, hd, one_mul]
  have he := WeierstrassDilatation.equation_map W s (π * b3) (π * b4) (π ^ 2 * b6) f
  rw [← hx, ← hy] at he
  apply ((isUnit_iff_exists_inv.mpr ⟨d, hd⟩).isRegular.pow 2).left
  simp only [map_mul, map_pow] at he ⊢
  linear_combination he

/-- The deeper divided chart maps by the actual preceding fractions x/π and y/π. -/
def fractionMap (f : B →ₐ[R] S) (d : S) (hd : algebraMap R S π * d = 1) : D →ₐ[R] S :=
  WeierstrassDilatation.evaluation W (s * π) b3 b4 b6 (d * f BX) (d * f BY)
    (fraction_equation W s π b3 b4 b6 f d hd)

/-- The deeper horizontal coordinate maps to x/π. -/
@[simp] theorem fractionMap_x (f : B →ₐ[R] S) (d : S)
    (hd : algebraMap R S π * d = 1) :
    fractionMap W s π b3 b4 b6 f d hd DX = d * f BX :=
  WeierstrassDilatation.evaluation_x _ _ _ _ _ _ _ _

/-- The deeper vertical coordinate maps to y/π. -/
@[simp] theorem fractionMap_y (f : B →ₐ[R] S) (d : S)
    (hd : algebraMap R S π * d = 1) :
    fractionMap W s π b3 b4 b6 f d hd DY = d * f BY :=
  WeierstrassDilatation.evaluation_y _ _ _ _ _ _ _ _

/-- Composing the fraction substitution with refinement recovers the preceding map. -/
theorem fractionMap_refinement (f : B →ₐ[R] S) (d : S)
    (hd : algebraMap R S π * d = 1) :
    (fractionMap W s π b3 b4 b6 f d hd).comp ref = f := by
  apply WeierstrassDilatation.hom_ext <;>
    simp [← mul_assoc, hd]

/-- A map out of the deeper chart is determined by refinement when π is regular. -/
theorem refinement_hom_ext (hπ : IsRegular (algebraMap R S π)) (f g : D →ₐ[R] S)
    (h : f.comp ref = g.comp ref) : f = g := by
  apply WeierstrassDilatation.hom_ext
  · apply hπ.left
    simpa only [AlgHom.comp_apply, WeierstrassDilatation.refinement_x, map_mul,
      AlgHom.commutes] using AlgHom.congr_fun h BX
  · apply hπ.left
    simpa only [AlgHom.comp_apply, WeierstrassDilatation.refinement_y, map_mul,
      AlgHom.commutes] using AlgHom.congr_fun h BY

end FLT.Mazur.WeierstrassSuccessiveScale
