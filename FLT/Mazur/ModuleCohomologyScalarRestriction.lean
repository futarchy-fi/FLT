/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomologyRing

/-!
# Composition of coefficient homomorphisms in actual cohomology

The cohomology types retain their coefficient maps. Factoring a map is
restriction of scalars on the unchanged underlying cohomology group.
-/

@[expose] public noncomputable section

open AlgebraicGeometry

namespace FLT.Mazur.FCurve

universe u

variable {X : Scheme.{u}} {R S : Type u} [CommRing R] [CommRing S]

/-- Factoring coefficients is restriction of scalars on actual cohomology. -/
def moduleRingHCompEquiv (φ : R →+* S) (σ : S →+* Γ(X, ⊤))
    (M : X.Modules) (q : ℕ) :
    let _ : Module R (ModuleRingH σ M q) := Module.compHom (ModuleRingH σ M q) φ
    ModuleRingH (σ.comp φ) M q ≃ₗ[R] ModuleRingH σ M q := by
  let _ : Module R (ModuleRingH σ M q) := Module.compHom (ModuleRingH σ M q) φ
  exact { toAddEquiv := AddEquiv.refl _, map_smul' := fun _ _ ↦ rfl }

/-- A proved factorization compares the original coefficient action to restricted scalars. -/
def moduleRingHFactorEquiv (ρ : R →+* Γ(X, ⊤)) (φ : R →+* S)
    (σ : S →+* Γ(X, ⊤)) (hρ : ρ = σ.comp φ) (M : X.Modules) (q : ℕ) :
    let _ : Module R (ModuleRingH σ M q) := Module.compHom (ModuleRingH σ M q) φ
    ModuleRingH ρ M q ≃ₗ[R] ModuleRingH σ M q :=
  hρ ▸ moduleRingHCompEquiv φ σ M q

end FLT.Mazur.FCurve
