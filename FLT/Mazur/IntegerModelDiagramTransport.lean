/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IntegerModelHomTransport
public import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Retaining diagram equations and covers under enlargement

Transport preserves identities and compositions, hence all already proved
diagram equations, including triple-overlap cocycles. Transition of marked
elements preserves principal covers and their explicit unit-ideal equations.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.Approximation

universe u v

variable {A B C D : Type u} [CommRing A] [CommRing B] [CommRing C] [CommRing D]
  [Algebra A B] [Algebra A C] [Algebra A D] {n m r t p q : ℕ}
  (P : Algebra.Presentation A B (Fin n) (Fin m))
  (Q : Algebra.Presentation A C (Fin r) (Fin t))
  (T : Algebra.Presentation A D (Fin p) (Fin q))
  {A₀ A₁ : Subalgebra ℤ A}
  [P.HasCoeffs A₀] [P.HasCoeffs A₁] [Q.HasCoeffs A₀] [Q.HasCoeffs A₁]
  [T.HasCoeffs A₀] [T.HasCoeffs A₁] (h : A₀ ≤ A₁)

/-- Identity maps of presentation models transport to identity maps. -/
@[simp]
theorem integerModelTransportHom_id :
    integerModelTransportHom P P h (AlgHom.id A₀ _) = AlgHom.id A₁ _ := by
  apply integerModel_hom_ext P h
  intro b
  simp only [integerModelTransportHom_transition, AlgHom.id_apply]

/-- Composition of model maps commutes with transport to larger coefficients. -/
@[simp]
theorem integerModelTransportHom_comp
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (g : Q.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀) :
    integerModelTransportHom P T h (g.comp f) =
      (integerModelTransportHom Q T h g).comp (integerModelTransportHom P Q h f) := by
  apply integerModel_hom_ext P h
  intro b
  simp only [integerModelTransportHom_transition, AlgHom.comp_apply]

/-- A fixed triangle relation, such as a triple-overlap cocycle, persists. -/
theorem integerModelTransportHom_triangle
    (f : P.ModelOfHasCoeffs A₀ →ₐ[A₀] Q.ModelOfHasCoeffs A₀)
    (g : Q.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀)
    (k : P.ModelOfHasCoeffs A₀ →ₐ[A₀] T.ModelOfHasCoeffs A₀) (hk : g.comp f = k) :
    (integerModelTransportHom Q T h g).comp (integerModelTransportHom P Q h f) =
      integerModelTransportHom P T h k := by
  rw [← integerModelTransportHom_comp, hk]

/-- Unit-ideal covering equations persist with their chosen coefficients. -/
theorem integerModelTransition_cover_equation {I : Type v} [Fintype I]
    (x c : I → P.ModelOfHasCoeffs A₀) (hc : ∑ i, c i * x i = 1) :
    ∑ i, integerModelTransition P h (c i) * integerModelTransition P h (x i) = 1 := by
  simpa only [map_sum, map_mul, map_one] using congrArg (integerModelTransition P h) hc

/-- Every family of principal opens covering a model still covers after transition. -/
theorem integerModelTransition_principal_cover {I : Type v}
    (x : I → P.ModelOfHasCoeffs A₀)
    (hx : (⨆ i, PrimeSpectrum.basicOpen (x i)) = ⊤) :
    (⨆ i, PrimeSpectrum.basicOpen (integerModelTransition P h (x i))) = ⊤ := by
  let F := TopologicalSpace.Opens.comap
    ⟨PrimeSpectrum.comap (integerModelTransition P h),
      PrimeSpectrum.continuous_comap (integerModelTransition P h)⟩
  have he := congrArg F hx
  simpa only [F, map_iSup, map_top, PrimeSpectrum.comap_basicOpen] using he

end FLT.Mazur.Approximation
