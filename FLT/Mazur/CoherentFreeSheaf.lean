/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.CoherentOpenDescent
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

/-! # Finite presentations of free module sheaves -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace FLT.Mazur.FCurve

/-- A finite free sheaf has its specified generators and no relations. -/
instance freeSheaf_isFinitePresentation (X : Scheme.{u}) (κ : Type u) [Finite κ] :
    (SheafOfModules.free (R := X.ringCatSheaf) κ).IsFinitePresentation := by
  let q := (SheafOfModules.free.generatingSections
    (R := X.ringCatSheaf) κ).localGeneratorsData.quasiCoherentData
  refine { exists_quasicoherentData := ⟨q, ?_⟩ }
  refine { isFinite_presentation := fun i ↦ ?_ }
  exact { isFiniteType_generators := ⟨inferInstanceAs (Finite κ)⟩
          isFiniteType_relations := ⟨inferInstanceAs (Finite (ULift Empty))⟩ }

/-- The structure module is finitely presented on every scheme. -/
instance unitSheaf_isFinitePresentation (X : Scheme.{u}) :
    (SheafOfModules.unit X.ringCatSheaf).IsFinitePresentation :=
  (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso
    (coproductUniqueIso (fun _ : PUnit.{u + 1} ↦ SheafOfModules.unit X.ringCatSheaf))
    (freeSheaf_isFinitePresentation X PUnit)

end FLT.Mazur.FCurve
