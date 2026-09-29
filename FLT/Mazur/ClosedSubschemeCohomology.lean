/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ClosedPushforwardCohomology
public import FLT.Mazur.FiniteAffineCoverDimension

/-!
# Cohomology consequences for closed subschemes

A finite affine cover of the ambient scheme bounds cohomology on a closed
subscheme. Finiteness over a specified base ring is equivalent to finiteness
of the closed direct image's cohomology. The latter equivalence does not
establish projective coherent finiteness.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules

universe u v

namespace FLT.Mazur.FCurve

variable {X Y : Scheme.{u}} [Y.IsSeparated] [IsLocallyNoetherian Y]
  (f : X ⟶ Y) [IsClosedImmersion f] (M : X.Modules) [M.IsFinitePresentation]

/-- An ambient finite affine cover bounds cohomology of a closed subscheme. -/
theorem closedSubscheme_moduleH_subsingleton {ι : Type u} [Fintype ι]
    (U : ι → Y.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)
    (n : ℕ) (hn : Fintype.card ι ≤ n) : Subsingleton (ModuleH M n) := by
  letI _coherent : ((pushforward f).obj M).IsFinitePresentation :=
    CoherentDevissage.closedPushforward_isFinitePresentation f M
  letI _vanishing := finiteAffineCover_moduleH_subsingleton
    ((pushforward f).obj M) U hU hCover n hn
  exact (closedPushforwardModuleHEquiv f M n).symm.toEquiv.injective.subsingleton

/-- Base-ring finiteness transfers in both directions through closed direct image. -/
theorem closedPushforward_moduleH_finite_iff {R : Type v} [Ring R]
    (ρ : R →+* Γ(Y, ⊤)) (n : ℕ) :
    letI _targetScalars := Module.compHom (ModuleH ((pushforward f).obj M) n) ρ
    letI _sourceScalars := Module.compHom (ModuleH M n) (f.appTop.hom.comp ρ)
    Module.Finite R (ModuleH ((pushforward f).obj M) n) ↔
      Module.Finite R (ModuleH M n) := by
  letI _targetScalars := Module.compHom (ModuleH ((pushforward f).obj M) n) ρ
  letI _sourceScalars := Module.compHom (ModuleH M n) (f.appTop.hom.comp ρ)
  constructor
  · intro h
    letI _finite := h
    exact Module.Finite.equiv (closedPushforwardRingHEquiv f M ρ n)
  · intro h
    letI _finite := h
    exact Module.Finite.equiv (closedPushforwardRingHEquiv f M ρ n).symm

end FLT.Mazur.FCurve
