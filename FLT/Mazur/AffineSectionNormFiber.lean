/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeTranslationNormFiber
public import Mathlib.AlgebraicGeometry.AffineScheme

/-!
# Full fibers of norms on affine scheme sections

The section algebra uses the actual scheme morphism. Its finite-free norm
is nonzero precisely when the section avoids every point of the original fiber.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Module
namespace FLT.Mazur.AffineSectionNormFiber
universe u v
set_option backward.isDefEq.respectTransparency false
variable {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y] (f : X ⟶ Y)

/-- The affine spectrum identification preserves the actual fiber map. -/
theorem spectrum_fiber (x : X) :
    PrimeSpectrum.comap f.appTop.hom (X.isoSpec.hom x) =
      Y.isoSpec.hom (f x) := by
  exact congrArg (fun g : X ⟶ Spec Γ(Y, ⊤) ↦ g x)
    (Scheme.isoSpec_hom_naturality f)

/-- Nonvanishing of the determinant norm tests the entire original scheme fiber. -/
theorem mem_basicOpen_norm_iff {ι : Type v} [Finite ι] :
    let _ := f.appTop.hom.toAlgebra
    ∀ (_b : Basis ι Γ(Y, ⊤) Γ(X, ⊤)) (s : Γ(X, ⊤)) (y : Y),
    y ∈ Y.basicOpen (Algebra.norm Γ(Y, ⊤) s) ↔
      ∀ x : X, f x = y → x ∈ X.basicOpen s := by
  let _ := f.appTop.hom.toAlgebra
  dsimp only
  intro b s y
  have hX (x : X) : x ∈ X.basicOpen s ↔ X.isoSpec.hom x ∈ PrimeSpectrum.basicOpen s := by
    rw [← X.map_PrimeSpectrum_basicOpen_of_affine]
    rfl
  have hY : y ∈ Y.basicOpen (Algebra.norm Γ(Y, ⊤) s) ↔
      Y.isoSpec.hom y ∈ PrimeSpectrum.basicOpen (Algebra.norm Γ(Y, ⊤) s) := by
    rw [← Y.map_PrimeSpectrum_basicOpen_of_affine]
    rfl
  rw [hY, FiniteFreeTranslationNorm.mem_basicOpen_norm_iff b]
  constructor
  · intro h x hx
    exact (hX x).mpr (h _ ((spectrum_fiber f x).trans (congrArg Y.isoSpec.hom hx)))
  · intro h q hq
    obtain ⟨x, rfl⟩ := X.isoSpec.hom.homeomorph.surjective q
    apply (hX x).mp
    apply h x
    apply Y.isoSpec.hom.homeomorph.injective
    exact (spectrum_fiber f x).symm.trans hq

end FLT.Mazur.AffineSectionNormFiber
