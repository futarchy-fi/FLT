/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CechFreeOpen
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Flasque

/-!
# Injective abelian sheaves are flasque

Free abelian sheaves on opens carry open inclusions to monomorphisms.
Injectivity therefore extends sections from any open to every larger open.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory TopologicalSpace Opposite

universe u

namespace FLT.Mazur.AbelianInjectiveFlasque

open CechFreeOpen

variable {X : TopCat.{u}}

/-- Free abelian sheaves carry inclusions of opens to monomorphisms. -/
instance mono_freeOpenMap {U V : Opens X} (i : U ⟶ V) : Mono (freeOpenMap i) := by
  have : Mono (Functor.whiskerRight (yoneda.map i) AddCommGrpCat.free) := by
    exact NatTrans.mono_of_mono_app _
  exact Functor.map_mono
    (presheafToSheaf (Opens.grothendieckTopology X) AddCommGrpCat) _

variable (I : TopCat.Sheaf AddCommGrpCat.{u} X) [Injective I]

/-- Every section of an injective abelian sheaf extends to a larger open. -/
lemma restriction_surjective {U V : Opens X} (i : U ⟶ V) :
    Function.Surjective (I.obj.map i.op) := by
  intro s
  let g : freeOpen U ⟶ I := (freeOpenHomEquiv U I).symm s
  let h : freeOpen V ⟶ I := Injective.factorThru g (freeOpenMap i)
  refine ⟨freeOpenHomEquiv V I h, ?_⟩
  rw [← freeOpenHomEquiv_naturality_open]
  change freeOpenHomEquiv U I
    (freeOpenMap i ≫ Injective.factorThru g (freeOpenMap i)) = s
  rw [Injective.comp_factorThru]
  exact (freeOpenHomEquiv U I).apply_symm_apply s

/-- An injective abelian sheaf is flasque. -/
instance isFlasque : TopCat.Sheaf.IsFlasque I where
  epi {U V} i := by
    apply (AddCommGrpCat.epi_iff_surjective _).mpr
    exact restriction_surjective I i.unop

end FLT.Mazur.AbelianInjectiveFlasque
