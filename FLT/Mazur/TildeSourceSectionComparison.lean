/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineSourceSectionComparison

/-!
# Original affine modules on source charts

The reconstruction unit and source-open tensor comparison identify the
original module tensored with source coordinates with the actual pullback
sections. The pure-tensor formula retains both adjunction units.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
open scoped TensorProduct ChangeOfRings

universe u

namespace FLT.Mazur.TildeSourceSectionComparison

open AffineModuleGlobalSections ModuleSourceSectionBaseChange

variable {X Y : Scheme.{u}} [IsAffine Y] (f : X ⟶ Y) (N : ModuleCat Γ(Y, ⊤))

/-- Scalar extension of the original module, before affine reconstruction. -/
def comparison (U : X.Opens) :
    (ModuleCat.extendScalars (scalarMap f U)).obj N ⟶
      ((pullback f).obj ((affineTilde Y).obj N)).val.obj (op U) :=
  (ModuleCat.extendScalars (scalarMap f U)).map ((affineAdjunction Y).unit.app N) ≫
    ModuleSourceSectionBaseChange.comparison f ((affineTilde Y).obj N) U

/-- The original module maps to the actual pullback through both canonical units. -/
lemma comparison_tmul (U : X.Opens) (r : Γ(X, U)) (n : N) :
    comparison f N U (r ⊗ₜ[Γ(Y, ⊤),scalarMap f U] n) =
      r • (show Γ((pullback f).obj ((affineTilde Y).obj N), U) from
        unitMap f ((affineTilde Y).obj N) U ((affineAdjunction Y).unit.app N n)) := by
  change ModuleSourceSectionBaseChange.comparison f ((affineTilde Y).obj N) U
    ((ModuleCat.extendScalars (scalarMap f U)).map ((affineAdjunction Y).unit.app N)
      (r ⊗ₜ[Γ(Y, ⊤),scalarMap f U] n)) = _
  rw [ModuleCat.ExtendScalars.map_tmul, ModuleSourceSectionBaseChange.comparison_tmul]

/-- The original-module comparison commutes with actual source restrictions. -/
lemma comparison_restrict {U V : X.Opens} (i : U ⟶ V) (r : Γ(X, V)) (n : N) :
    ((pullback f).obj ((affineTilde Y).obj N)).presheaf.map i.op
      (comparison f N V (r ⊗ₜ[Γ(Y, ⊤),scalarMap f V] n)) =
    comparison f N U ((X.presheaf.map i.op r) ⊗ₜ[Γ(Y, ⊤),scalarMap f U] n) := by
  rw [comparison_tmul, comparison_tmul, map_smul, unitMap_restrict]

/-- Reconstruction followed by source base change is invertible on affine opens. -/
lemma comparison_isIso (U : X.affineOpens) : IsIso (comparison f N U.1) := by
  let _ := ModuleSourceSectionBaseChange.comparison_isIso f ((affineTilde Y).obj N) U
  unfold comparison
  infer_instance

/-- The scalar-extended original module identifies with the actual affine pullback sections. -/
def sectionsIso (U : X.affineOpens) :
    (ModuleCat.extendScalars (scalarMap f U.1)).obj N ≅
      ((pullback f).obj ((affineTilde Y).obj N)).val.obj (op U.1) := by
  let _ := comparison_isIso f N U
  exact asIso (comparison f N U.1)

/-- Ordinary tensor order, with the original module first, gives the same section group. -/
def tensorSectionsEquiv (U : X.affineOpens) :
    let := (scalarMap f U.1).toAlgebra
    N ⊗[Γ(Y, ⊤)] Γ(X, U.1) ≃+
      Γ((pullback f).obj ((affineTilde Y).obj N), U.1) := by
  let := (scalarMap f U.1).toAlgebra
  exact (TensorProduct.comm Γ(Y, ⊤) N Γ(X, U.1)).toAddEquiv.trans
    (sectionsIso f N U).toLinearEquiv.toAddEquiv

/-- The tensor identification keeps the original module element and source scalar. -/
lemma tensorSectionsEquiv_tmul (U : X.affineOpens) (n : N) (r : Γ(X, U.1)) :
    let := (scalarMap f U.1).toAlgebra
    tensorSectionsEquiv f N U (n ⊗ₜ[Γ(Y, ⊤)] r) =
      r • (show Γ((pullback f).obj ((affineTilde Y).obj N), U.1) from
        unitMap f ((affineTilde Y).obj N) U.1 ((affineAdjunction Y).unit.app N n)) := by
  let := (scalarMap f U.1).toAlgebra
  exact comparison_tmul f N U.1 r n

/-- The tensor comparison also accepts a proved equal presentation of the structural map. -/
def tensorSectionsEquivOfMap (U : X.affineOpens) (φ : Γ(Y, ⊤) →+* Γ(X, U.1))
    (hφ : φ = scalarMap f U.1) :
    let := φ.toAlgebra
    N ⊗[Γ(Y, ⊤)] Γ(X, U.1) ≃+
      Γ((pullback f).obj ((affineTilde Y).obj N), U.1) := by
  subst φ
  exact tensorSectionsEquiv f N U

/-- Changing the presentation of the structural map preserves the pure-tensor formula. -/
lemma tensorSectionsEquivOfMap_tmul (U : X.affineOpens) (φ : Γ(Y, ⊤) →+* Γ(X, U.1))
    (hφ : φ = scalarMap f U.1) (n : N) (r : Γ(X, U.1)) :
    let := φ.toAlgebra
    tensorSectionsEquivOfMap f N U φ hφ (n ⊗ₜ[Γ(Y, ⊤)] r) =
      r • (show Γ((pullback f).obj ((affineTilde Y).obj N), U.1) from
        unitMap f ((affineTilde Y).obj N) U.1 ((affineAdjunction Y).unit.app N n)) := by
  subst φ
  exact tensorSectionsEquiv_tmul f N U n r

end FLT.Mazur.TildeSourceSectionComparison
