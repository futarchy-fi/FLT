/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomologyRing

/-!
# Exact cohomology over a Noetherian base ring

Restrict the actual connecting homomorphism along a specified base-ring map.
The long exact sequence gives the missing finite subobject and middle-term
arguments, including the injective degree-zero endpoint.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

local instance ringExactHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : Scheme.{u}} {R : Type u} [CommRing R] (ρ : R →+* Γ(X, ⊤))
  (S : ShortComplex X.Modules) (hS : S.ShortExact)

/-- The actual connecting map, linear for the specified base-ring action. -/
def moduleRingHConnecting (n : ℕ) :
    ModuleRingH ρ S.X₃ n →ₗ[R] ModuleRingH ρ S.X₁ (n + 1) where
  toFun := moduleHConnecting S (CoherentDevissage.moduleToSheaf_shortExact hS) n
  map_add' := (moduleHConnecting S (CoherentDevissage.moduleToSheaf_shortExact hS) n).map_add
  map_smul' r x :=
    (moduleHConnecting S (CoherentDevissage.moduleToSheaf_shortExact hS) n).map_smul (ρ r) x

include hS in
/-- Exactness at middle cohomology after restriction of scalars. -/
lemma moduleRingH_exact_middle (n : ℕ) :
    Function.Exact ((moduleRingHFunctor ρ n).map S.f)
      ((moduleRingHFunctor ρ n).map S.g) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₂' (CoherentDevissage.moduleToSheaf_shortExact hS) n)

/-- Exactness before the connecting map over the specified ring. -/
lemma moduleRingH_exact_right (n : ℕ) :
    Function.Exact ((moduleRingHFunctor ρ n).map S.g) (moduleRingHConnecting ρ S hS n) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₃' (CoherentDevissage.moduleToSheaf_shortExact hS)
      n (n + 1) rfl)

/-- Exactness after the connecting map over the specified ring. -/
lemma moduleRingH_exact_left (n : ℕ) :
    Function.Exact (moduleRingHConnecting ρ S hS n)
      ((moduleRingHFunctor ρ (n + 1)).map S.f) :=
  (ShortComplex.ab_exact_iff_function_exact _).mp
    (Sheaf.H.longSequence_exact₁' (CoherentDevissage.moduleToSheaf_shortExact hS)
      n (n + 1) rfl)

include hS in
/-- The first degree-zero map is injective, without any Noetherian hypothesis. -/
lemma moduleRingHMap_zero_injective :
    Function.Injective ((moduleRingHFunctor ρ 0).map S.f) := by
  have hAb : (moduleAbelianComplex S).ShortExact :=
    CoherentDevissage.moduleToSheaf_shortExact hS
  have := hAb.mono_f
  exact Abelian.Ext.postcomp_mk₀_injective_of_mono _ (moduleAbelianComplex S).f

variable [IsNoetherianRing R]

include hS

/-- Finite outer cohomology modules give a finite middle module. -/
theorem moduleRingH_finite_middle (n : ℕ)
    [Module.Finite R ((moduleRingHFunctor ρ n).obj S.X₁)]
    [Module.Finite R ((moduleRingHFunctor ρ n).obj S.X₃)] :
    Module.Finite R (ModuleRingH ρ S.X₂ n) :=
  moduleFinite_of_exact_pair _ _ (moduleRingH_exact_middle ρ S hS n)

/-- Positive-degree subobject cohomology is finite from the two adjacent terms. -/
theorem moduleRingH_finite_left_succ (n : ℕ)
    [Module.Finite R ((moduleRingHFunctor ρ n).obj S.X₃)]
    [Module.Finite R ((moduleRingHFunctor ρ (n + 1)).obj S.X₂)] :
    Module.Finite R (ModuleRingH ρ S.X₁ (n + 1)) := by
  let : Module.Finite R (ModuleRingH ρ S.X₃ n) :=
    inferInstanceAs (Module.Finite R ((moduleRingHFunctor ρ n).obj S.X₃))
  exact moduleFinite_of_exact_pair _ _ (moduleRingH_exact_left ρ S hS n)

/-- At degree zero, finite middle cohomology suffices. -/
theorem moduleRingH_finite_left_zero
    [Module.Finite R ((moduleRingHFunctor ρ 0).obj S.X₂)] :
    Module.Finite R (ModuleRingH ρ S.X₁ 0) :=
  Module.Finite.of_injective ((moduleRingHFunctor ρ 0).map S.f).hom
    (moduleRingHMap_zero_injective ρ S hS)

end FLT.Mazur.FCurve
