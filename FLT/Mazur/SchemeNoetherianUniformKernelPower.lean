/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeQuasiCompactOpenKernelPower
public import FLT.Mazur.SchemeEffectiveEpiSections
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# One power annihilating an entire open restriction kernel

Noetherian affine coordinates make the whole restriction kernel finitely
generated. A finite affine cover then gives one exponent for every section
on a Noetherian scheme, with no Noetherian assumption on its global sections.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.SchemeNoetherianUniformKernelPower
universe u

/-- Noetherian global coordinates give a coefficient-independent power annihilator. -/
theorem exists_uniform_power_of_noetherian_coordinates
    {U X : Scheme.{u}} [CompactSpace X] [IsNoetherianRing Γ(X, ⊤)]
    (f : U ⟶ X) [IsOpenImmersion f] (a : Γ(X, ⊤))
    (ha : X.basicOpen a ≤ f.opensRange) :
    ∃ k : ℕ, ∀ z : Γ(X, ⊤), f.appTop z = 0 → a ^ k * z = 0 := by
  classical
  let K := RingHom.ker f.appTop.hom
  obtain ⟨s, hs⟩ := IsNoetherian.noetherian K
  have hz (z : s) : f.appTop z.val = 0 := by
    change z.val ∈ K
    rw [← hs]
    exact Submodule.subset_span z.property
  obtain ⟨k, hk⟩ := SchemeQuasiCompactOpenKernelPower.exists_pow_mul_eq_zero_finite
    f a (fun z : s ↦ z.val) ha hz
  have hK : a ^ k ∈ K.annihilator := by
    rw [← hs, Submodule.mem_annihilator_span]
    exact hk
  exact ⟨k, fun z hz ↦ Submodule.mem_annihilator.mp hK z hz⟩

/-- Every section vanishing on an open shares one power on the full Noetherian scheme. -/
theorem exists_uniform_power {X : Scheme.{u}} [IsNoetherian X]
    (O : X.Opens) (a : Γ(X, ⊤)) (ha : X.basicOpen a ≤ O) :
    ∃ k : ℕ, ∀ z : Γ(X, ⊤), O.ι.appTop z = 0 → a ^ k * z = 0 := by
  classical
  let C := X.affineCover.finiteSubcover
  have hlocal (i : C.I₀) : ∃ k : ℕ, ∀ z : Γ(X, ⊤), O.ι.appTop z = 0 →
      (C.f i).appTop a ^ k * (C.f i).appTop z = 0 := by
    let _ : IsAffine (C.X i) := isAffine_Spec _
    let _ := isLocallyNoetherian_of_isOpenImmersion (C.f i)
    let _ := IsLocallyNoetherian.component_noetherian
      (⟨⊤, isAffineOpen_top (C.X i)⟩ : (C.X i).affineOpens)
    have hai : (C.X i).basicOpen ((C.f i).appTop a) ≤ C.f i ⁻¹ᵁ O := by
      rw [← Scheme.preimage_basicOpen_top]
      exact fun _ hx ↦ ha hx
    obtain ⟨k, hk⟩ := exists_uniform_power_of_noetherian_coordinates
      (C.f i ⁻¹ᵁ O).ι ((C.f i).appTop a)
      (by simpa only [Scheme.Opens.opensRange_ι] using hai)
    refine ⟨k, fun z hz ↦ hk _ ?_⟩
    change ((C.f i ⁻¹ᵁ O).ι ≫ C.f i).appTop z = 0
    rw [← morphismRestrict_ι, Scheme.Hom.comp_appTop,
      ConcreteCategory.comp_apply, hz, map_zero]
  choose k hk using hlocal
  refine ⟨Finset.univ.sup k, fun z hz ↦ ?_⟩
  have he (i : C.I₀) : (C.f i).appTop (a ^ Finset.univ.sup k * z) =
      (C.f i).appTop 0 := by
    have hi : k i ≤ Finset.univ.sup k := Finset.le_sup (f := k) (Finset.mem_univ i)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi
    rw [map_mul, map_pow, map_zero, hj, pow_add,
      mul_comm ((C.f i).appTop a ^ k i), mul_assoc, hk i z hz, mul_zero]
  apply (SchemeEffectiveEpiSections.functionEquiv X).symm.injective
  apply C.hom_ext
  intro i
  apply (SchemeEffectiveEpiSections.functionEquiv (C.X i)).injective
  simpa only [SchemeEffectiveEpiSections.functionEquiv_comp, Equiv.apply_symm_apply] using he i

/-- One exponent clears all open equalities, including infinitely many chosen coefficients. -/
theorem exists_uniform_power_eq {X : Scheme.{u}} [IsNoetherian X]
    (O : X.Opens) (a : Γ(X, ⊤)) (ha : X.basicOpen a ≤ O) :
    ∃ k : ℕ, ∀ z w : Γ(X, ⊤), O.ι.appTop z = O.ι.appTop w →
      a ^ k * z = a ^ k * w := by
  obtain ⟨k, hk⟩ := exists_uniform_power O a ha
  refine ⟨k, fun z w hzw ↦ ?_⟩
  apply sub_eq_zero.mp
  rw [← mul_sub]
  exact hk (z - w) (by rw [map_sub, hzw, sub_self])

end FLT.Mazur.SchemeNoetherianUniformKernelPower
