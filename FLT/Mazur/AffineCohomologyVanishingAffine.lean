/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCohomologyVanishingSpectrum
public import FLT.Mazur.SchemeCohomologyIso

/-!
# Positive-degree module cohomology vanishes on affine schemes

For an arbitrary affine scheme, the canonical isomorphism with the spectrum
of global sections transports a module to a module on a spectrum. Restriction
preserves quasi-coherence, and the scheme-isomorphism comparison identifies
the actual Ext-based cohomology groups. Spectrum vanishing therefore gives
vanishing in every positive degree without finiteness assumptions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

variable {X : Scheme.{u}} [IsAffine X]

/-- The module on the canonical spectrum, transported by the module equivalence. -/
abbrev affineSpectrumModule (M : X.Modules) : (Spec Γ(X, ⊤)).Modules :=
  (SchemeCohomologyIso.moduleEquivalence X.isoSpec.symm).functor.obj M

instance affineSpectrumModuleQuasicoherent (M : X.Modules) [M.IsQuasicoherent] :
    (affineSpectrumModule M).IsQuasicoherent :=
  inferInstanceAs (M.restrict X.isoSpec.inv).IsQuasicoherent

/-- Cohomology of a module agrees with that of its canonical spectrum transport. -/
def affineSpectrumModuleHEquiv (M : X.Modules) (n : ℕ) :
    ModuleH M n ≃+ ModuleH (affineSpectrumModule M) n :=
  moduleHIsoEquiv X.isoSpec.symm M n

/-- Quasi-coherent modules on any affine scheme have zero positive-degree cohomology. -/
theorem affine_moduleH_succ_subsingleton (M : X.Modules) [M.IsQuasicoherent] (q : ℕ) :
    Subsingleton (ModuleH M (q + 1)) := by
  have := quasicoherent_moduleH_succ_subsingleton (affineSpectrumModule M) q
  exact (affineSpectrumModuleHEquiv M (q + 1)).injective.subsingleton

/-- The positive-degree formulation for an arbitrary degree index. -/
theorem affine_moduleH_subsingleton (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (hn : 0 < n) : Subsingleton (ModuleH M n) := by
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
  exact affine_moduleH_succ_subsingleton M q

/-- Every positive-degree module cohomology class on an affine scheme is zero. -/
theorem affine_moduleH_eq_zero (M : X.Modules) [M.IsQuasicoherent]
    (n : ℕ) (hn : 0 < n) (x : ModuleH M n) : x = 0 := by
  have := affine_moduleH_subsingleton M n hn
  exact Subsingleton.elim _ _

end FLT.Mazur.FCurve
