/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.NoetherianDirectSumSheaf
public import FLT.Mazur.AffineBasisSumCoproduct

/-!
# Original sectionwise module sums on a Noetherian scheme

Compactness of every open makes the degreewise presheaf a module sheaf.
Its module action is the original pointwise structure-sheaf action.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped DirectSum

universe u

namespace FLT.Mazur.NoetherianModuleSum

variable {X : Scheme.{u}} (M : ℕ → X.Modules)

/-- The degreewise module presheaf with the original restrictions and scalar actions. -/
def presheaf : PresheafOfModules X.ringCatSheaf.obj := by
  let P := FiniteCoverDirectSum.presheaf (fun n ↦ (M n).presheaf)
  let _ (U : X.Opensᵒᵖ) : Module (X.ringCatSheaf.obj.obj U) (P.obj U) :=
    inferInstanceAs (Module Γ(X, U.unop) (⨁ n, Γ(M n, U.unop)))
  exact PresheafOfModules.ofPresheaf P (by
    intro U V f r s
    apply DFinsupp.ext
    intro n
    exact (M n).map_smul f.unop r (s n))

variable [TopologicalSpace.NoetherianSpace X]

/-- The pointwise module sum, justified by Noetherian compactness. -/
def sum : X.Modules :=
  ⟨presheaf M, NoetherianDirectSum.isSheaf X (fun n ↦ (M n).presheaf)
    (fun n ↦ (M n).isSheaf)⟩

/-- Its affine restriction is exactly the original affine degree sum. -/
def basisIso : AffineBasisModuleMorphism.basis (sum M) ≅ AffineBasisDirectSum.sum M :=
  ObjectProperty.isoMk _ (NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
    intro U V f
    rfl))

/-- The sectionwise module sum is the categorical sheaf coproduct. -/
def coproductIso : sum M ≅ ∐ M :=
  AffineBasisSumMaps.coproductIso M (sum M) (basisIso M) (by
    intro U r s
    rfl)

end FLT.Mazur.NoetherianModuleSum
