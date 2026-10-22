/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeScalarImageNilpotence
public import FLT.Mazur.SchemeScalarAvoidanceCover
public import Mathlib.RingTheory.Ideal.Operations

/-!
# Exact scalar kernels of finite point covers

A finite family of compact schemes covering every point detects the radical
of the original scalar kernel. The coefficient rings are not reduced, and
the exact kernels need not agree before taking radicals.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeScalarPrincipalNeighborhood
variable {R : Type} [CommRing R] {X : Scheme.{0}} [CompactSpace X]
  {ι : Type} [Finite ι] {Y : ι → Scheme.{0}} [∀ i, CompactSpace (Y i)]
  (φ : ∀ i, Y i ⟶ X) (σ : R →+* Γ(X, ⊤))

/-- Finite full coefficient kernels detect precisely the original scalar nilpotence. -/
theorem finite_cover_scalar_kernel_radical
    (hcover : ∀ x : X, ∃ i, ∃ y : Y i, φ i y = x) :
    (⨅ i, RingHom.ker ((φ i).appTop.hom.comp σ)).radical =
      (RingHom.ker σ).radical := by
  classical
  let _ := Fintype.ofFinite ι
  have hinf : (⨅ i, RingHom.ker ((φ i).appTop.hom.comp σ)).radical =
      ⨅ i, (RingHom.ker ((φ i).appTop.hom.comp σ)).radical := by
    simpa only [Finset.inf_univ_eq_iInf, Ideal.radicalInfTopHom_apply,
      Function.comp_def] using map_finset_inf (Ideal.radicalInfTopHom (R := R))
        Finset.univ (fun i ↦ RingHom.ker ((φ i).appTop.hom.comp σ))
  rw [hinf]
  apply le_antisymm
  · intro a ha
    rw [← scalarImage_vanishingIdeal_eq_kernel_radical σ,
      PrimeSpectrum.mem_vanishingIdeal]
    rintro P ⟨x, rfl⟩
    obtain ⟨i, y, rfl⟩ := hcover x
    have hi := Ideal.mem_iInf.mp ha i
    rw [← scalarImage_vanishingIdeal_eq_kernel_radical,
      PrimeSpectrum.mem_vanishingIdeal] at hi
    apply hi
    refine ⟨y, ?_⟩
    rw [scalarMorphism_comp]
    rfl
  · apply le_iInf
    intro i
    apply Ideal.radical_mono
    intro a ha
    change (φ i).appTop (σ a) = 0
    rw [show σ a = 0 from ha, map_zero]

end FLT.Mazur.SchemeScalarPrincipalNeighborhood
