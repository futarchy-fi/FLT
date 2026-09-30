/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoherentSubmoduleRestriction

/-!
# Annihilators in actual affine sections

The submodule killed by a finitely generated ideal commutes with localization.
Applied to the actual global sections of a coherent affine sheaf, this gives a
finitely presented coefficient module and its canonical coherent inclusion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry

universe u

namespace FLT.Mazur.AffineAnnihilator

section Algebra

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N]

/-- The submodule of elements killed by every scalar in the ideal. -/
def annihilated (J : Ideal R) (M : Type*) [AddCommGroup M] [Module R M] : Submodule R M where
  carrier := {m | ∀ r ∈ J, r • m = 0}
  zero_mem' := by simp
  add_mem' := by intro x y hx hy r hr; simp [smul_add, hx r hr, hy r hr]
  smul_mem' := by intro a x hx r hr; rw [smul_comm, hx r hr, smul_zero]

@[simp]
lemma mem_annihilated (J : Ideal R) (m : M) :
    m ∈ annihilated J M ↔ ∀ r ∈ J, r • m = 0 := Iff.rfl

/-- It suffices to test a generating set of the ideal. -/
lemma mem_annihilated_span (s : Set R) (m : M) :
    m ∈ annihilated (Ideal.span s) M ↔ ∀ r ∈ s, r • m = 0 := by
  constructor
  · intro h r hr
    exact h r (Ideal.subset_span hr)
  · intro h r hr
    induction hr using Submodule.span_induction with
    | mem r hr => exact h r hr
    | zero => exact zero_smul _ _
    | add r t _ _ hr ht => rw [add_smul, hr, ht, add_zero]
    | smul a r _ hr => rw [smul_eq_mul, mul_smul, hr, smul_zero]

/-- Finitely many vanishing localized scalar multiples have one common denominator. -/
lemma common_denominator (S : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule S f]
    (s : Finset R) (m : M) (h : ∀ r ∈ s, f (r • m) = 0) :
    ∃ t : S, ∀ r ∈ s, r • (t • m) = 0 := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨t, ht⟩ := ih (fun r hr ↦ h r (Finset.mem_insert_of_mem hr))
    obtain ⟨v, hv⟩ := (IsLocalizedModule.eq_iff_exists S f).mp
      ((h a (Finset.mem_insert_self a s)).trans (map_zero f).symm)
    simp only [Submonoid.smul_def, smul_zero] at hv
    refine ⟨v * t, ?_⟩
    intro r hr
    rcases Finset.mem_insert.mp hr with rfl | hr
    · rw [mul_smul, Submonoid.smul_def, Submonoid.smul_def,
        smul_comm r, smul_comm r, smul_comm (v : R), hv, smul_zero]
    · rw [mul_smul, Submonoid.smul_def, smul_comm r, ht r hr, smul_zero]

/-- Membership in the localized annihilator is annihilation after localization. -/
theorem mem_localized_annihilated (J : Ideal R) (hJ : J.FG)
    (S : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule S f] (n : N) :
    n ∈ (annihilated J M).localized₀ S f ↔ ∀ r ∈ J, r • n = 0 := by
  constructor
  · rintro ⟨m, hm, t, rfl⟩ r hr
    rw [← IsLocalizedModule.mk'_smul, hm r hr, IsLocalizedModule.mk'_zero]
  · intro hn
    obtain ⟨s, hs⟩ := hJ
    obtain ⟨⟨m, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective S f n
    dsimp only [Function.uncurry] at hn
    have h (r : R) (hr : r ∈ s) : f (r • m) = 0 := by
      rw [map_smul, ← IsLocalizedModule.mk'_cancel' f m t, smul_comm]
      rw [hn r (hs ▸ Ideal.subset_span hr), smul_zero]
    obtain ⟨v, hv⟩ := common_denominator S f s m h
    refine ⟨v • m, ?_, v * t, IsLocalizedModule.mk'_cancel_left f m v t⟩
    rw [← hs, mem_annihilated_span]
    exact hv

/-- The comparison as submodules of the localized ambient module. -/
theorem localized_annihilated (J : Ideal R) (hJ : J.FG)
    (S : Submonoid R) (f : M →ₗ[R] N) [IsLocalizedModule S f] :
    (annihilated J M).localized₀ S f = annihilated J N := by
  ext n
  exact mem_localized_annihilated J hJ S f n

/-- Testing the extended ideal is equivalent to testing the original scalars. -/
lemma mem_annihilated_map (J : Ideal R) (A : Type*) [CommRing A] [Algebra R A]
    [Module A N] [IsScalarTower R A N] (n : N) :
    n ∈ annihilated (J.map (algebraMap R A)) N ↔ ∀ r ∈ J, r • n = 0 := by
  have h (K : Ideal A) : (∀ a ∈ K, a • n = 0) ↔
      K ≤ (Submodule.span A {n}).annihilator := by
    simp only [IsConcreteLE.le_iff, Submodule.mem_annihilator_span_singleton]
  rw [mem_annihilated, h, Ideal.map_le_iff_le_comap]
  simp only [IsConcreteLE.le_iff, Ideal.mem_comap, Submodule.mem_annihilator_span_singleton,
    algebraMap_smul]

/-- Localization identifies the coefficient annihilator with that of the extended ideal. -/
theorem localized_annihilated_map (J : Ideal R) (hJ : J.FG)
    (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A] [IsLocalization S A]
    [Module A N] [IsScalarTower R A N] (f : M →ₗ[R] N) [IsLocalizedModule S f] :
    (annihilated J M).localized' A S f = annihilated (J.map (algebraMap R A)) N := by
  ext n
  exact (mem_localized_annihilated J hJ S f n).trans (mem_annihilated_map J A n).symm

/-- Over a Noetherian ring the annihilator in a finite module is finitely presented. -/
theorem annihilated_finitePresentation [IsNoetherianRing R] [Module.Finite R M]
    (J : Ideal R) : Module.FinitePresentation R (annihilated J M) :=
  Module.finitePresentation_of_finite R (annihilated J M)

end Algebra

section Affine

variable {R : CommRingCat.{u}} (J : Ideal R) (F : (Spec R).Modules)

/-- The annihilator in the given sheaf's actual affine section module. -/
abbrev sections : Submodule R (moduleSpecΓFunctor.obj F) :=
  annihilated J (moduleSpecΓFunctor.obj F)

/-- The actual coefficient module is finite. -/
theorem sections_finite [IsNoetherianRing R] [F.IsFinitePresentation] :
    Module.Finite R (sections J F) := by
  have : Module.Finite R (moduleSpecΓFunctor.obj F) :=
    FCurve.affineCoherent_finite_sections F
  exact inferInstance

/-- The actual coefficient module is finitely presented. -/
theorem sections_finitePresentation [IsNoetherianRing R] [F.IsFinitePresentation] :
    Module.FinitePresentation R (sections J F) := by
  have : Module.Finite R (moduleSpecΓFunctor.obj F) :=
    FCurve.affineCoherent_finite_sections F
  exact annihilated_finitePresentation J

/-- The affine annihilator sheaf is constructed from actual sections. -/
abbrev sheaf : (Spec R).Modules := tilde (ModuleCat.of R (sections J F))

/-- Its inclusion is the coefficient inclusion followed by the canonical counit. -/
def inclusion : sheaf J F ⟶ F :=
  AffineCoherentSubmoduleRestriction.coefficientInclusion F (sections J F)

instance inclusion_mono [F.IsQuasicoherent] : Mono (inclusion J F) :=
  AffineCoherentSubmoduleRestriction.coefficientInclusion_mono F (sections J F)

/-- The constructed affine subsheaf is coherent. -/
theorem sheaf_coherent [IsNoetherianRing R] [F.IsFinitePresentation] :
    (sheaf J F).IsFinitePresentation := by
  have := sections_finitePresentation J F
  exact FCurve.affineTilde_isFinitePresentation _

/-- The localization comparison for the actual section module, with its scalar extension. -/
theorem sections_localized (hJ : J.FG) (S : Submonoid R) :
    (sections J F).localized S =
      annihilated (J.map (algebraMap R (Localization S)))
        (LocalizedModule S (moduleSpecΓFunctor.obj F)) :=
  localized_annihilated_map J hJ S (Localization S) (LocalizedModule.mkLinearMap S _)

end Affine

end FLT.Mazur.AffineAnnihilator
