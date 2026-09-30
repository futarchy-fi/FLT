/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleFreeOpen
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Injective module sheaves are flasque

A section of an injective module sheaf over an open extends across every
inclusion of opens: its representing morphism extends across the corresponding
free-open monomorphism. Thus the underlying abelian sheaf is flasque.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite

universe u

namespace FLT.Mazur.ModuleInjectiveFlasque

open ModuleFreeOpen

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
  (I : SheafOfModules.{u} R) [Injective I]

/-- Every section of an injective module sheaf extends to a larger open. -/
lemma restriction_surjective {U V : Opens X} (i : U ⟶ V) :
    Function.Surjective (I.val.map i.op) := by
  intro s
  let g : freeOpen R U ⟶ I := (freeOpenHomEquiv R U I).symm s
  let h : freeOpen R V ⟶ I := Injective.factorThru g (freeOpenMap R i)
  refine ⟨freeOpenHomEquiv R V I h, ?_⟩
  rw [← freeOpenHomEquiv_naturality_open]
  change freeOpenHomEquiv R U I
    (freeOpenMap R i ≫ Injective.factorThru g (freeOpenMap R i)) = s
  rw [Injective.comp_factorThru]
  exact (freeOpenHomEquiv R U I).apply_symm_apply s

/-- The underlying abelian sheaf of an injective module sheaf is flasque. -/
instance isFlasque_toSheaf : TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj I) where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact restriction_surjective I i.unop

/-- Restrictions of the underlying abelian sheaf are surjective. -/
lemma underlying_restriction_surjective {U V : Opens X} (i : U ⟶ V) :
    Function.Surjective (((SheafOfModules.toSheaf R).obj I).obj.map i.op) :=
  restriction_surjective I i

end FLT.Mazur.ModuleInjectiveFlasque
