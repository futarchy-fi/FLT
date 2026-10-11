/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.IdealPowerScalarLift
public import FLT.Mazur.ModuleCohomologyRing
public import Mathlib.RingTheory.Nakayama

/-!
# Cohomology of a regular scalar quotient

The actual scalar endomorphism induces the original scalar action on
cohomology. Its long exact sequence detects regularity and vanishing of
finite cohomology without replacing it by a completion.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace FLT.Mazur.PrincipalScalarCohomology

open FCurve IdealPowerScalarLift

universe u

set_option backward.isDefEq.respectTransparency false

local instance scalarQuotientHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} (M : X.Modules) (r : Γ(X, ⊤))
  [Mono (scalarEnd M r)]

/-- The scalar quotient sequence retains multiplication as its first arrow. -/
def sequence : ShortComplex X.Modules := ShortComplex.cokernelSequence (scalarEnd M r)

/-- Regularity on the coefficient sheaf gives the actual scalar short exact sequence. -/
theorem sequence_shortExact : (sequence M r).ShortExact :=
  { exact := ShortComplex.cokernelSequence_exact (scalarEnd M r)
    mono_f := inferInstanceAs (Mono (scalarEnd M r))
    epi_g := inferInstanceAs (Epi (cokernel.π (scalarEnd M r))) }

/-- The scalar quotient sequence is also short exact on underlying abelian sheaves. -/
theorem sequence_abelian_shortExact : (moduleAbelianComplex (sequence M r)).ShortExact :=
  CoherentDevissage.moduleToSheaf_shortExact (sequence_shortExact M r)

/-- Cohomology classes killed by quotient restriction are exactly original scalar multiples. -/
theorem scalar_exact (q : ℕ) :
    Function.Exact (fun x : ModuleH M q ↦ r • x)
      (moduleHMap (cokernel.π (scalarEnd M r)) q) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₂' (sequence_abelian_shortExact M r) q)

/-- Lifting quotient cohomology in degree q makes the scalar regular in degree q+1. -/
theorem scalar_regular (q : ℕ)
    (hq : Function.Surjective (moduleHMap (cokernel.π (scalarEnd M r)) q))
    (x : ModuleH M (q + 1)) (hx : r • x = 0) : x = 0 := by
  let S := sequence M r
  let hS := sequence_abelian_shortExact M r
  have h₁ : Function.Exact (moduleHConnecting S hS q)
      (moduleHMap S.f (q + 1)) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₁' hS q (q + 1) rfl)
  obtain ⟨y, hy⟩ := (h₁ x).mp hx
  obtain ⟨z, rfl⟩ := hq y
  have h₃ : Function.Exact (moduleHMap S.g q) (moduleHConnecting S hS q) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' hS q (q + 1) rfl)
  exact hy.symm.trans ((h₃ _).mpr ⟨z, rfl⟩)

/-- Vanishing of the next original cohomology makes actual quotient restriction surjective. -/
theorem quotient_surjective (q : ℕ) [Subsingleton (ModuleH M (q + 1))] :
    Function.Surjective (moduleHMap (cokernel.π (scalarEnd M r)) q) := by
  have he : Function.Exact (moduleHMap (sequence M r).g q)
      (moduleHConnecting (sequence M r) (sequence_abelian_shortExact M r) q) :=
    (ShortComplex.ab_exact_iff_function_exact _).mp
      (Sheaf.H.longSequence_exact₃' (sequence_abelian_shortExact M r) q (q + 1) rfl)
  intro x
  exact (he x).mp (Subsingleton.elim (α := ModuleH M (q + 1)) _ _)

/-- Finite original cohomology vanishes if its regular scalar quotient vanishes. -/
theorem finite_vanishing {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
    (a : R) (ha : a ∈ Ideal.jacobson (⊥ : Ideal R)) (q : ℕ)
    [Mono (scalarEnd M (ρ a))] [Module.Finite R (ModuleRingH ρ M q)]
    [Subsingleton (ModuleH (cokernel (scalarEnd M (ρ a))) q)] :
    Subsingleton (ModuleRingH ρ M q) := by
  have hs : Function.Surjective (fun x : ModuleRingH ρ M q ↦ a • x) := by
    intro x
    exact (scalar_exact M (ρ a) q x).mp (Subsingleton.elim _ _)
  have ht := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot
    (Ideal.span {a}) (⊤ : Submodule R (ModuleRingH ρ M q)) Module.Finite.fg_top
    (by
      intro x _
      obtain ⟨y, rfl⟩ := hs x
      exact Submodule.smul_mem_smul (Ideal.subset_span (Set.mem_singleton a))
        Submodule.mem_top)
    ((Ideal.span_singleton_le_iff_mem _).mpr ha)
  have hz (x : ModuleRingH ρ M q) : x = 0 := by
    have hx : x ∈ (⊤ : Submodule R (ModuleRingH ρ M q)) := Submodule.mem_top
    rwa [ht, Submodule.mem_bot] at hx
  exact ⟨fun x y ↦ (hz x).trans (hz y).symm⟩

end FLT.Mazur.PrincipalScalarCohomology
