/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineCoverCohomology
public import FLT.Mazur.FiniteCechCyclesScalars
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness from affine-cover terms

Over a Noetherian base ring, a finite degree-n Cech term has finite cycles and
finite homology. For an affine cover of a separated scheme this gives finiteness
of actual module cohomology. Only the degree under consideration needs a finite
term; finite intersection sections suffice when the cover index is finite.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite

universe u v

namespace FLT.Mazur.FCurve

open CechSheafHZero

variable {X : Scheme.{u}} {ι : Type u} (M : X.Modules) (U : ι → X.Opens)
  {R : Type v} [Ring R] (ρ : R →+* Γ(X, ⊤))

/-- Finiteness of a term implies finiteness of its cycles over a Noetherian base. -/
theorem finiteCechRingCycles_finite [IsNoetherianRing R] (n : ℕ) :
    letI _termModule := Module.compHom ((C U (moduleAbelianSheaf M)).X n) ρ
    Module.Finite R ((C U (moduleAbelianSheaf M)).X n) →
      Module.Finite R (finiteCechRingCycles M U ρ n) := by
  let _termModule := Module.compHom ((C U (moduleAbelianSheaf M)).X n) ρ
  intro h
  let _finiteTerm := h
  infer_instance

/-- Homology is a quotient of the finite cycle submodule, including in degree zero. -/
theorem finiteCechRingHomology_finite [IsNoetherianRing R] (n : ℕ) :
    letI _termModule := Module.compHom ((C U (moduleAbelianSheaf M)).X n) ρ
    letI _homologyModule := Module.compHom (CH U (moduleAbelianSheaf M) n) ρ
    Module.Finite R ((C U (moduleAbelianSheaf M)).X n) →
      Module.Finite R (CH U (moduleAbelianSheaf M) n) := by
  let _termModule := Module.compHom ((C U (moduleAbelianSheaf M)).X n) ρ
  let _homologyModule := Module.compHom (CH U (moduleAbelianSheaf M) n) ρ
  intro h
  let _finiteCycles := finiteCechRingCycles_finite M U ρ n h
  exact Module.Finite.equiv (finiteCechRingHomologyEquiv M U ρ n).symm

/-- A finite product of finite intersection sections gives a finite Cech term. -/
theorem finiteCechRingTerm_finite [Finite ι] (n : ℕ) :
    letI _termModule := Module.compHom ((C U (moduleAbelianSheaf M)).X n) ρ
    letI _sectionModule := fun a : Fin (n + 1) → ι ↦
      Module.compHom (M.val.obj (op (V U n a)))
        ((X.presheaf.map (V U n a).leTop.op).hom.comp ρ)
    (∀ a : Fin (n + 1) → ι, Module.Finite R (M.val.obj (op (V U n a)))) →
      Module.Finite R ((C U (moduleAbelianSheaf M)).X n) := by
  let _termModule := Module.compHom ((C U (moduleAbelianSheaf M)).X n) ρ
  let _sectionModule := fun a : Fin (n + 1) → ι ↦
    Module.compHom (M.val.obj (op (V U n a)))
      ((X.presheaf.map (V U n a).leTop.op).hom.comp ρ)
  intro h
  let _finiteSections := h
  let _coordinateModule (a : Fin (n + 1) → ι) :
      Module R ((moduleAbelianSheaf M).obj.obj (op (V U n a))) := _sectionModule a
  let _finiteCoordinates (a : Fin (n + 1) → ι) :
      Module.Finite R ((moduleAbelianSheaf M).obj.obj (op (V U n a))) := h a
  exact Module.Finite.equiv (finiteCechRingTermEquiv M U ρ n).symm

variable [X.IsSeparated] [M.IsQuasicoherent]
  (hU : ∀ i, IsAffineOpen (U i)) (hCover : iSup U = ⊤)

include hU hCover in
/-- The constructed affine-cover comparison transfers term finiteness to H^n. -/
theorem affineCoverModuleH_finite [IsNoetherianRing R] (n : ℕ) :
    letI _termModule := Module.compHom ((C U (moduleAbelianSheaf M)).X n) ρ
    letI _cohomologyModule := Module.compHom (ModuleH M n) ρ
    Module.Finite R ((C U (moduleAbelianSheaf M)).X n) →
      Module.Finite R (ModuleH M n) := by
  let _termModule := Module.compHom ((C U (moduleAbelianSheaf M)).X n) ρ
  let _homologyModule := Module.compHom (CH U (moduleAbelianSheaf M) n) ρ
  let _cohomologyModule := Module.compHom (ModuleH M n) ρ
  intro h
  let _finiteHomology := finiteCechRingHomology_finite M U ρ n h
  exact Module.Finite.equiv (affineCoverRingCechEquiv M U hU hCover ρ n)

end FLT.Mazur.FCurve
