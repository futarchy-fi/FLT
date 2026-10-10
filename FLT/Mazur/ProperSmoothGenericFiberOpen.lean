/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GenericConnectedFiberOpen
public import FLT.Mazur.IdealPowerExtensionCharts

/-!
# Generic connected-fiber openness for proper smooth pointed families

Properness supplies the finite affine cover and separatedness used by the
generic comparison. The resulting nonzero principal open needs no cover input.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.Approximation

variable {R : CommRingCat.{0}} [IsNoetherianRing R] [IsDomain R]
  {X : Scheme.{0}} (f : X ⟶ Spec R) [IsProper f] [Smooth f]
  (s : Spec R ⟶ X) (hs : s ≫ f = 𝟙 _)

include s hs in
/-- Proper smooth pointed families have an open connected-fiber locus on a generic open. -/
theorem exists_generic_isOpen_connectedFiber :
    ∃ r : R, r ≠ 0 ∧ IsOpen
      (geometricallyConnectedLocus f ∩ (PrimeSpectrum.basicOpen r : Set (PrimeSpectrum R))) := by
  let _ : IsNoetherian X := Chow.source_isNoetherian f
  let _ : X.IsSeparated := ⟨by
    rw [← terminal.comp_from f]
    infer_instance⟩
  obtain ⟨ι, hι, V, hV⟩ := IdealPowerExtensionCharts.exists_finite_affine_cover (X := X)
  let _ : Finite ι := hι
  let _ : Fintype ι := Fintype.ofFinite ι
  let _ : LinearOrder ι := LinearOrder.lift' (Fintype.equivFin ι) (Fintype.equivFin ι).injective
  exact exists_generic_isOpen_connectedFiber_inter f (fun i ↦ (V i).1) (fun i ↦ (V i).2) hV s hs

end FLT.Mazur.Approximation
