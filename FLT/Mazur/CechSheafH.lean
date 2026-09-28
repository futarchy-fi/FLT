/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomology
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Degree-zero Cech comparison

For an open cover, the kernel of the first Cech differential consists of compatible
families of sections. Gluing identifies this group with Ext-based `Sheaf.H F 0`.
The comparison is natural in the abelian coefficient sheaf, hence in coefficient
multiplication. Higher-degree comparison and the categorical complex adapter are
separate steps.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u v

namespace FLT.Mazur.CechSheafH

variable {X : TopCat.{u}} {ι : Type u}
variable (F : TopCat.Sheaf AddCommGrpCat.{u} X) (U : ι → Opens X)

/-- The first unnormalized Cech differential, with the ordered-pair indexing. -/
def differentialZero : (∀ i, F.obj.obj (op (U i))) →+
    (∀ p : ι × ι, F.obj.obj (op (U p.1 ⊓ U p.2))) where
  toFun s p := F.obj.map (homOfLE inf_le_right).op (s p.2) -
    F.obj.map (homOfLE inf_le_left).op (s p.1)
  map_zero' := by ext p; simp
  map_add' s t := by ext p; simp [sub_add_sub_comm]

/-- Cech zero-cocycles; there are no boundaries entering degree zero. -/
def zeroCocycles : AddSubgroup (∀ i, F.obj.obj (op (U i))) :=
  (differentialZero F U).ker

lemma mem_zeroCocycles_iff (s : ∀ i, F.obj.obj (op (U i))) :
    s ∈ zeroCocycles F U ↔ TopCat.Presheaf.IsCompatible F.obj U s := by
  simp only [zeroCocycles, AddMonoidHom.mem_ker, differentialZero,
    AddMonoidHom.coe_mk, ZeroHom.coe_mk, funext_iff, Pi.zero_apply, sub_eq_zero,
    TopCat.Presheaf.IsCompatible]
  exact ⟨fun h i j ↦ (h (i, j)).symm, fun h p ↦ (h p.1 p.2).symm⟩

/-- Restriction of a global section to a compatible family. -/
def restrictZero : F.obj.obj (op ⊤) →+ zeroCocycles F U where
  toFun s := ⟨fun i ↦ F.obj.map (homOfLE le_top).op s, by
    rw [mem_zeroCocycles_iff]
    intro i j
    simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp]
    rfl⟩
  map_zero' := by ext i; exact map_zero _
  map_add' s t := by ext i; exact map_add _ s t

lemma restrictZero_bijective (hU : iSup U = ⊤) :
    Function.Bijective (restrictZero F U) := by
  constructor
  · intro s t h
    apply F.eq_of_locally_eq' U ⊤ (fun _ ↦ homOfLE le_top) (ge_of_eq hU)
    intro i
    exact congrArg (fun z : zeroCocycles F U ↦ z.val i) h
  · intro s
    obtain ⟨t, ht, _⟩ := F.existsUnique_gluing' U ⊤ (fun _ ↦ homOfLE le_top)
      (ge_of_eq hU) s.val ((mem_zeroCocycles_iff F U s.val).mp s.property)
    exact ⟨t, Subtype.ext (funext ht)⟩

/-- Gluing and restriction identify global sections with Cech zero-cocycles. -/
def sectionsEquiv (hU : iSup U = ⊤) : F.obj.obj (op ⊤) ≃+ zeroCocycles F U :=
  AddEquiv.ofBijective (restrictZero F U) (restrictZero_bijective F U hU)

variable {F} {G : TopCat.Sheaf AddCommGrpCat.{u} X}

/-- A coefficient morphism acts on Cech zero-cocycles componentwise. -/
def zeroCocyclesMap (f : F ⟶ G) : zeroCocycles F U →+ zeroCocycles G U where
  toFun s := ⟨fun i ↦ f.hom.app (op (U i)) (s.val i), by
    rw [mem_zeroCocycles_iff]
    intro i j
    have h := (mem_zeroCocycles_iff F U s.val).mp s.property i j
    simpa only [ConcreteCategory.comp_apply, NatTrans.naturality_apply] using
      congrArg (f.hom.app (op (U i ⊓ U j))) h⟩
  map_zero' := by ext i; exact map_zero _
  map_add' s t := by ext i; exact map_add _ _ _

@[simp]
lemma zeroCocyclesMap_apply (f : F ⟶ G) (s : zeroCocycles F U) (i : ι) :
    (zeroCocyclesMap U f s).val i = f.hom.app (op (U i)) (s.val i) := rfl

lemma restrictZero_naturality (f : F ⟶ G) (s : F.obj.obj (op ⊤)) :
    zeroCocyclesMap U f (restrictZero F U s) =
      restrictZero G U (f.hom.app (op ⊤) s) := by
  ext i
  exact ConcreteCategory.congr_hom (f.hom.naturality (homOfLE le_top).op) s

variable [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]

/-- Ext-based degree-zero cohomology is the kernel of the first Cech differential. -/
def hZeroEquiv (hU : iSup U = ⊤) : Sheaf.H F 0 ≃+ zeroCocycles F U :=
  (Sheaf.H.equiv₀ F isTerminalTop).trans (sectionsEquiv F U hU)

/-- The degree-zero comparison is natural for every coefficient morphism. -/
lemma hZeroEquiv_naturality (hU : iSup U = ⊤) (f : F ⟶ G) (x : Sheaf.H F 0) :
    hZeroEquiv U hU (Sheaf.H.map f 0 x) =
      zeroCocyclesMap U f (hZeroEquiv U hU x) := by
  change restrictZero G U (Sheaf.H.equiv₀ G isTerminalTop (Sheaf.H.map f 0 x)) = _
  rw [← Sheaf.H.equiv₀_naturality isTerminalTop f]
  exact (restrictZero_naturality U f _).symm

end FLT.Mazur.CechSheafH

namespace FLT.Mazur.FCurve

open AlgebraicGeometry

local instance cechModuleHasExt (X : AlgebraicGeometry.Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

variable {X : AlgebraicGeometry.Scheme.{u}} {ι : Type u}
variable (M : X.Modules) (U : ι → Opens X) (hU : iSup U = ⊤)

/-- The Cech zero-cocycle comparison for the module cohomology used in FC08. -/
def moduleCechHZeroEquiv : ModuleH M 0 ≃+
    CechSheafH.zeroCocycles (moduleAbelianSheaf M) U :=
  CechSheafH.hZeroEquiv U hU

/-- Multiplication acts on Cech families through its actual coefficient morphism. -/
lemma moduleCechHZeroEquiv_multiply (r : Γ(X, ⊤)) (x : ModuleH M 0) :
    moduleCechHZeroEquiv M U hU (r • x) =
      CechSheafH.zeroCocyclesMap U (moduleMultiply M r)
        (moduleCechHZeroEquiv M U hU x) :=
  CechSheafH.hZeroEquiv_naturality U hU (moduleMultiply M r) x

end FLT.Mazur.FCurve
