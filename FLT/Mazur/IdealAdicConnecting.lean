/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealAdicFormalRange
public import FLT.Mazur.ModuleRingCohomologyExact

/-!
# Actual connecting maps in the ideal-adic quotient tower

The lifting obstruction is the connecting homomorphism into next-degree power
cohomology. Its naturality uses the original power and quotient transitions.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open FLT.Mazur.FCurve FLT.Mazur.GlobalIdealPower
open FLT.Mazur.GlobalIdealPowerCompatibility

universe u

namespace FLT.Mazur.IdealAdicQuotient

local instance connectingHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} [IsLocallyNoetherian X]
  {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (I : X.IdealSheafData) (M : X.Modules) [M.IsFinitePresentation]

/-- The original connecting map for the quotient by the n-th ideal power. -/
def quotientConnecting (q n : ℕ) :
    ModuleRingH ρ (quotient I M n) q →ₗ[R] ModuleRingH ρ (power I n M) (q + 1) :=
  moduleRingHConnecting ρ (ShortComplex.cokernelSequence (inclusion (I ^ n) M))
    (quotient_shortExact I M n) q

/-- Vanishing of the original connecting map is precisely liftability. -/
lemma quotientConnecting_eq_zero_iff (q n : ℕ) (x : ModuleRingH ρ (quotient I M n) q) :
    quotientConnecting ρ I M q n x = 0 ↔
      ∃ y : ModuleRingH ρ M q, moduleHMap (projection I M n) q y = x :=
  moduleRingH_exact_right ρ (ShortComplex.cokernelSequence (inclusion (I ^ n) M))
    (quotient_shortExact I M n) q x

/-- Every connecting class is killed by the original power inclusion. -/
lemma inclusion_quotientConnecting (q n : ℕ) (x : ModuleRingH ρ (quotient I M n) q) :
    moduleHMap (inclusion (I ^ n) M) (q + 1) (quotientConnecting ρ I M q n x) = 0 := by
  exact (moduleRingH_exact_left ρ
    (ShortComplex.cokernelSequence (inclusion (I ^ n) M))
    (quotient_shortExact I M n) q _).mpr ⟨x, rfl⟩

/-- Original transitions give a morphism between the underlying abelian short complexes. -/
def quotientAbelianSequenceMap {a b : ℕ} (h : a ≤ b) :
    moduleAbelianComplex (ShortComplex.cokernelSequence (inclusion (I ^ b) M)) ⟶
      moduleAbelianComplex (ShortComplex.cokernelSequence (inclusion (I ^ a) M)) where
  τ₁ := (CoherentDevissage.moduleToSheaf X).map (transition I M h)
  τ₂ := (CoherentDevissage.moduleToSheaf X).map (𝟙 M)
  τ₃ := (CoherentDevissage.moduleToSheaf X).map (reduction I M h)
  comm₁₂ := by
    change (CoherentDevissage.moduleToSheaf X).map (transition I M h) ≫
      (CoherentDevissage.moduleToSheaf X).map (inclusion (I ^ a) M) =
        (CoherentDevissage.moduleToSheaf X).map (inclusion (I ^ b) M) ≫
          (CoherentDevissage.moduleToSheaf X).map (𝟙 M)
    rw [← Functor.map_comp, ← Functor.map_comp, transition_comp, Category.comp_id]
  comm₂₃ := by
    change (CoherentDevissage.moduleToSheaf X).map (𝟙 M) ≫
      (CoherentDevissage.moduleToSheaf X).map (projection I M a) =
        (CoherentDevissage.moduleToSheaf X).map (projection I M b) ≫
          (CoherentDevissage.moduleToSheaf X).map (reduction I M h)
    rw [← Functor.map_comp, ← Functor.map_comp, Category.id_comp, projection_reduction]

/-- Connecting maps commute with the actual quotient and power reductions. -/
lemma quotientConnecting_reduction (q : ℕ) {a b : ℕ} (h : a ≤ b)
    (x : ModuleRingH ρ (quotient I M b) q) :
    quotientConnecting ρ I M q a (moduleHMap (reduction I M h) q x) =
      moduleHMap (transition I M h) (q + 1) (quotientConnecting ρ I M q b x) :=
  Sheaf.H.δ_naturality q (q + 1) rfl
    (CoherentDevissage.moduleToSheaf_shortExact (quotient_shortExact I M b))
    (CoherentDevissage.moduleToSheaf_shortExact (quotient_shortExact I M a))
    (quotientAbelianSequenceMap I M h) x

/-- Eventual vanishing on the genuine power kernels makes quotient classes lift. -/
theorem eventual_lifts_of_power_kernel_vanishing (q : ℕ)
    (h : ∀ n, ∃ m, ∃ hnm : n ≤ m,
      ∀ z : ModuleRingH ρ (power I m M) (q + 1),
        moduleHMap (inclusion (I ^ m) M) (q + 1) z = 0 →
          moduleHMap (transition I M hnm) (q + 1) z = 0) :
    ∀ n, ∃ m, ∃ hnm : n ≤ m,
      ∀ z : ModuleRingH ρ (quotient I M m) q,
        ∃ x : ModuleRingH ρ M q,
          moduleHMap (projection I M n) q x = moduleHMap (reduction I M hnm) q z := by
  intro n
  obtain ⟨m, hnm, hm⟩ := h n
  refine ⟨m, hnm, fun z ↦ ?_⟩
  apply (quotientConnecting_eq_zero_iff ρ I M q n _).mp
  rw [quotientConnecting_reduction]
  exact hm _ (inclusion_quotientConnecting ρ I M q m z)

end FLT.Mazur.IdealAdicQuotient
