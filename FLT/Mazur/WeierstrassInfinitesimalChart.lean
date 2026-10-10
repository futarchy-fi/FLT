/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.WeierstrassInfinitySquareZero
public import FLT.Mazur.WeierstrassProjectiveChartProduct

/-!
# The actual infinitesimal identity chart

Maps from the original Y-chart reducing to the identity modulo a square-zero
ideal are parametrized by the ideal itself. The parameter is the original X
coordinate; its Z coordinate vanishes. These are actual algebra maps, not
formal points introduced independently of the cubic.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.WeierstrassIntegralChart

open WeierstrassCurve

variable {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
  (W : WeierstrassCurve R) (I : Ideal A) (hI : I ^ 2 = ⊥)

/-- Chart maps whose X and Z coordinates vanish modulo the infinitesimal ideal. -/
def InfinitesimalChart :=
  {f : Coordinate W 1 →ₐ[R] A // f (coord W 1 0) ∈ I ∧ f (coord W 1 2) ∈ I}

include hI

/-- Every infinitesimal X parameter solves the cubic with Z equal to zero. -/
theorem infinitesimalChart_equation (x : I) :
    (W.map (algebraMap R A)).toProjective.Equation ![(x : A), 1, 0] := by
  have h2 := squareZero_mul I hI x.property x.property
  have h3 : (x : A) ^ 3 = 0 := by rw [pow_succ, pow_two, h2, zero_mul]
  simp [Projective.equation_iff, Projective.fin3_def_ext, h3]

/-- The parameter gives an actual algebra map from the original cubic chart. -/
def infinitesimalChartPoint (x : I) : InfinitesimalChart W I :=
  ⟨evaluation W 1 ![(x : A), 1, 0] (infinitesimalChart_equation W I hI x) rfl,
    by simp⟩

/-- Its parameter is the original X coordinate. -/
@[simp] theorem infinitesimalChartPoint_x (x : I) :
    (infinitesimalChartPoint W I hI x).val (coord W 1 0) = (x : A) :=
  by simp [infinitesimalChartPoint]

/-- Every actual infinitesimal chart map has zero Z coordinate. -/
theorem infinitesimalChart_z (f : InfinitesimalChart W I) : f.val (coord W 1 2) = 0 := by
  apply infinitySquareZero_z (W.map (algebraMap R A)) I hI f.property.1 f.property.2
  have he := projective_equation_of_hom W 1 f.val
  have hv : f.val ∘ coord W 1 = ![f.val (coord W 1 0), 1, f.val (coord W 1 2)] := by
    ext i
    fin_cases i <;> simp [Projective.fin3_def_ext]
  rwa [hv] at he

/-- The square-zero ideal parametrizes precisely the actual infinitesimal identity chart. -/
def infinitesimalChartEquiv : I ≃ InfinitesimalChart W I where
  toFun := infinitesimalChartPoint W I hI
  invFun f := ⟨f.val (coord W 1 0), f.property.1⟩
  left_inv x := Subtype.ext (infinitesimalChartPoint_x W I hI x)
  right_inv f := by
    apply Subtype.ext
    apply hom_ext
    intro i
    fin_cases i
    · exact infinitesimalChartPoint_x W I hI _
    · simp [infinitesimalChartPoint]
    · simpa [infinitesimalChartPoint] using (infinitesimalChart_z W I hI f).symm

omit hI in
/-- The coordinate condition is exactly reduction to the original identity section. -/
theorem infinitesimalChart_iff_reduction (f : Coordinate W 1 →ₐ[R] A) :
    (f (coord W 1 0) ∈ I ∧ f (coord W 1 2) ∈ I) ↔
      (Ideal.Quotient.mkₐ R I).comp f = chartInfinityEvaluation W := by
  constructor
  · rintro ⟨hx, hz⟩
    apply hom_ext
    intro i
    fin_cases i <;> simp [AlgHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, hx, hz,
      Projective.fin3_def_ext]
  · intro h
    have hx := congrArg (fun g : Coordinate W 1 →ₐ[R] A ⧸ I ↦ g (coord W 1 0)) h
    have hz := congrArg (fun g : Coordinate W 1 →ₐ[R] A ⧸ I ↦ g (coord W 1 2)) h
    simpa [AlgHom.comp_apply, Ideal.Quotient.eq_zero_iff_mem, Projective.fin3_def_ext]
      using And.intro hx hz

end FLT.Mazur.WeierstrassIntegralChart
