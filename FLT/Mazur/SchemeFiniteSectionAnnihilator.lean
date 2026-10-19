/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianFiniteFamilyAnnihilator
public import FLT.Mazur.SchemeEffectiveEpiSections
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Finite scalar tests on a Noetherian scheme

A finite affine cover selects finitely many members of any family of global
sections that detect every global annihilator. The global coordinate ring
need not be Noetherian, and no reduction of the scheme is taken.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeFiniteSectionAnnihilator
universe u v

/-- Finitely many original sections detect the annihilator of the entire family. -/
theorem exists_finset_annihilator {X : Scheme.{u}} [IsNoetherian X]
    {ι : Type v} (a : ι → Γ(X, ⊤)) :
    ∃ s : Finset ι, ∀ r : Γ(X, ⊤),
      (∀ i ∈ s, r * a i = 0) ↔ ∀ i, r * a i = 0 := by
  classical
  let C := X.affineCover.finiteSubcover
  have hlocal (j : C.I₀) : ∃ s : Finset ι, ∀ r : Γ(C.X j, ⊤),
      (∀ i ∈ s, r * (C.f j).appTop (a i) = 0) ↔
        ∀ i, r * (C.f j).appTop (a i) = 0 := by
    let _ : IsAffine (C.X j) := isAffine_Spec _
    let _ := isLocallyNoetherian_of_isOpenImmersion (C.f j)
    let _ := IsLocallyNoetherian.component_noetherian
      (⟨⊤, isAffineOpen_top (C.X j)⟩ : (C.X j).affineOpens)
    exact NoetherianFiniteFamilyAnnihilator.exists_finset_annihilator
      (R := Γ(C.X j, ⊤)) (fun i ↦ (C.f j).appTop (a i))
  choose s hs using hlocal
  refine ⟨Finset.univ.biUnion s, fun r ↦ ⟨fun h i ↦ ?_, fun h i _ ↦ h i⟩⟩
  have he (j : C.I₀) : (C.f j).appTop (r * a i) = (C.f j).appTop 0 := by
    rw [map_mul, map_zero]
    apply (hs j _).mp _ i
    intro k hk
    have hz := congrArg (fun z ↦ (C.f j).appTop z)
      (h k (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ j, hk⟩))
    simpa only [map_mul, map_zero] using hz
  apply (SchemeEffectiveEpiSections.functionEquiv X).symm.injective
  apply C.hom_ext
  intro j
  apply (SchemeEffectiveEpiSections.functionEquiv (C.X j)).injective
  simpa only [SchemeEffectiveEpiSections.functionEquiv_comp, Equiv.apply_symm_apply] using he j

/-- Scalar tests may come from any ring; no finiteness over that ring is needed. -/
theorem exists_finset_scalar_tests {X : Scheme.{u}} [IsNoetherian X]
    {ι : Type v} (a : ι → Γ(X, ⊤)) {R : Type*} [CommRing R]
    (σ : R →+* Γ(X, ⊤)) :
    ∃ s : Finset ι, ∀ r : R, (∀ i ∈ s, σ r * a i = 0) ↔
      ∀ i, σ r * a i = 0 := by
  obtain ⟨s, hs⟩ := exists_finset_annihilator a
  exact ⟨s, fun r ↦ hs (σ r)⟩

end FLT.Mazur.SchemeFiniteSectionAnnihilator
