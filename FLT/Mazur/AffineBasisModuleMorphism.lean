/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineBasisSheafExtension
public import Mathlib.AlgebraicGeometry.Modules.Sheaf

/-!
# Extending linear morphisms from the affine basis

An additive sheaf morphism that is structure-linear on affine opens is
linear on every open. Thus compatible affine linear maps extend uniquely
to morphisms of the original module sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules

universe u

namespace FLT.Mazur.AffineBasisModuleMorphism

variable {X : Scheme.{u}} (M N : X.Modules)

/-- Linearity on the affine basis implies structure-linearity on every open. -/
lemma linear_of_affine (a : M.presheaf ⟶ N.presheaf)
    (h : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (s : Γ(M, U.1)),
      a.app (.op U.1) (r • s) = r • a.app (.op U.1) s)
    (V : X.Opens) (r : Γ(X, V)) (s : Γ(M, V)) :
    a.app (.op V) (r • s) = r • a.app (.op V) s := by
  apply N.isSheaf.section_ext
  intro x hx
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUV⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hx V.isOpen
  change U ≤ V at hUV
  refine ⟨U, hUV, hxU, ?_⟩
  have ha (t : Γ(M, V)) := ConcreteCategory.congr_hom
    (a.naturality (homOfLE hUV).op) t
  simp only [ConcreteCategory.comp_apply] at ha
  rw [← ha, M.map_smul, h ⟨U, hU⟩, N.map_smul, ha]

/-- Upgrade the original additive map using its affine scalar compatibility. -/
def ofAdditive (a : M.presheaf ⟶ N.presheaf)
    (h : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (s : Γ(M, U.1)),
      a.app (.op U.1) (r • s) = r • a.app (.op U.1) s) : M ⟶ N :=
  ⟨PresheafOfModules.homMk a (fun U r s ↦ linear_of_affine M N a h U.unop r s)⟩

/-- The upgrade retains the original additive map on every open. -/
lemma ofAdditive_app (a : M.presheaf ⟶ N.presheaf)
    (h : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (s : Γ(M, U.1)),
      a.app (.op U.1) (r • s) = r • a.app (.op U.1) s) (U : X.Opens) :
    (ofAdditive M N a h).app U = a.app (.op U) := rfl

/-- Restriction of an actual module's underlying sheaf to the affine basis. -/
def basis (M : X.Modules) : Sheaf (AffineBasis.topology X) AddCommGrpCat.{u} :=
  (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.obj
    ((SheafOfModules.toSheaf X.ringCatSheaf).obj M)

/-- Extend an additive affine map between the underlying actual module sheaves. -/
def additiveExtension (a : basis M ⟶ basis N) : M.presheaf ⟶ N.presheaf :=
  ((AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.preimage a).hom

/-- The extension recovers exactly the supplied maps on affine sections. -/
lemma additiveExtension_app (a : basis M ⟶ basis N) (U : X.affineOpens) :
    (additiveExtension M N a).app (.op U.1) = a.hom.app (.op U) :=
  congrArg (fun k ↦ k.hom.app (.op U))
    ((AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.map_preimage a)

/-- Compatible structure-linear affine maps extend to an actual module sheaf morphism. -/
def extend (a : basis M ⟶ basis N)
    (h : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (s : Γ(M, U.1)),
      a.hom.app (.op U) (r • s) =
        r • (show Γ(N, U.1) from a.hom.app (.op U) s)) : M ⟶ N :=
  ofAdditive M N (additiveExtension M N a) (by
    intro U r s
    rw [additiveExtension_app]
    exact h U r s)

/-- The linear extension has the original affine components. -/
lemma extend_app (a : basis M ⟶ basis N)
    (h : ∀ (U : X.affineOpens) (r : Γ(X, U.1)) (s : Γ(M, U.1)),
      a.hom.app (.op U) (r • s) =
        r • (show Γ(N, U.1) from a.hom.app (.op U) s)) (U : X.affineOpens) :
    (extend M N a h).app U.1 = a.hom.app (.op U) :=
  additiveExtension_app M N a U

/-- Module sheaf maps are determined by their components on the affine basis. -/
lemma hom_ext {a b : M ⟶ N} (h : ∀ U : X.affineOpens, a.app U.1 = b.app U.1) : a = b := by
  apply (SheafOfModules.toSheaf X.ringCatSheaf).map_injective
  apply (AffineBasis.sheafEquivalence X AddCommGrpCat).inverse.map_injective
  apply ObjectProperty.hom_ext
  apply NatTrans.ext
  funext U
  exact h U.unop

end FLT.Mazur.AffineBasisModuleMorphism
