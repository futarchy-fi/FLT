/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisFiniteCover
public import FLT.Mazur.AffineBasisModuleMorphism
public import Mathlib.Algebra.DirectSum.Module

/-!
# The sum of module sheaves on the affine basis

Finite subcovers make the pointwise sum a sheaf on the affine basis.
Its injections and descent maps use the original degreewise restrictions.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped DirectSum

universe u

namespace FLT.Mazur.AffineBasisDirectSum


variable {X : Scheme.{u}} (M : ℕ → X.Modules)

/-- The genuine affine-basis sheaf of finitely supported original sections. -/
abbrev sum : Sheaf (AffineBasis.topology X) AddCommGrpCat.{u} :=
  ⟨FiniteCoverDirectSum.presheaf (fun n ↦ (AffineBasisModuleMorphism.basis (M n)).obj),
    AffineBasis.directSum_isSheaf X _
      (fun n ↦ (AffineBasisModuleMorphism.basis (M n)).property)⟩

/-- The original degree inclusion on the affine basis. -/
def ι (n : ℕ) : AffineBasisModuleMorphism.basis (M n) ⟶ sum M where
  hom :=
    { app := fun U ↦ AddCommGrpCat.ofHom (DirectSum.of (fun k ↦ Γ(M k, U.unop.1)) n)
      naturality := by
        intro U V f
        apply ConcreteCategory.hom_ext
        intro s
        exact (DirectSum.map_of
          (fun k ↦ ((M k).presheaf.map (homOfLE (show V.unop.1 ≤ U.unop.1 from f.unop.le)).op).hom)
          n s).symm }

/-- A family of module sheaf maps acts on the sum by finite addition. -/
def desc {N : X.Modules} (a : ∀ n, M n ⟶ N) :
    sum M ⟶ AffineBasisModuleMorphism.basis N where
  hom :=
    { app := fun U ↦ AddCommGrpCat.ofHom
        (DirectSum.toAddMonoid (fun n ↦ (a n).app U.unop.1 |>.hom))
      naturality := by
        intro U V f
        apply ConcreteCategory.hom_ext
        intro s
        induction s using DirectSum.induction_on with
        | zero => simp
        | of n s =>
          change Γ(M n, U.unop.1) at s
          change DirectSum.toAddMonoid (fun k ↦ (a k).app V.unop.1 |>.hom)
              (DirectSum.map
                (fun k ↦ ((M k).presheaf.map
                  (homOfLE (show V.unop.1 ≤ U.unop.1 from f.unop.le)).op).hom)
                (DirectSum.of (fun k ↦ Γ(M k, U.unop.1)) n s)) =
            (N.presheaf.map (homOfLE (show V.unop.1 ≤ U.unop.1 from f.unop.le)).op)
              (DirectSum.toAddMonoid (fun k ↦ (a k).app U.unop.1 |>.hom)
                (DirectSum.of (fun k ↦ Γ(M k, U.unop.1)) n s))
          rw [DirectSum.map_of, DirectSum.toAddMonoid_of, DirectSum.toAddMonoid_of]
          exact ConcreteCategory.congr_hom
            (((SheafOfModules.toSheaf X.ringCatSheaf).map (a n)).hom.naturality
              (homOfLE (show V.unop.1 ≤ U.unop.1 from f.unop.le)).op) s
        | add s t hs ht => simpa only [map_add] using congrArg₂ (· + ·) hs ht }

/-- Finite addition recovers each supplied degree map. -/
lemma ι_desc {N : X.Modules} (a : ∀ n, M n ⟶ N) (n : ℕ) :
    ι M n ≫ desc M a =
      (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.map
        ((SheafOfModules.toSheaf X.ringCatSheaf).map (a n)) := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  exact DirectSum.toAddMonoid_of (fun k ↦ (a k).app U.unop.1 |>.hom) n s

/-- Maps out of the affine sum are determined on the original degree inclusions. -/
lemma hom_ext {N : Sheaf (AffineBasis.topology X) AddCommGrpCat.{u}}
    {a b : sum M ⟶ N} (h : ∀ n, ι M n ≫ a = ι M n ≫ b) : a = b := by
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  apply ConcreteCategory.hom_ext
  intro s
  induction s using DirectSum.induction_on with
  | zero => exact (map_zero (a.hom.app U).hom).trans (map_zero (b.hom.app U).hom).symm
  | of n s =>
      exact ConcreteCategory.congr_hom
        (congrArg (fun k ↦ k.hom.app U) (h n)) s
  | add s t hs ht => simpa only [map_add] using congrArg₂ (· + ·) hs ht

end FLT.Mazur.AffineBasisDirectSum
