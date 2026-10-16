/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatGlobalSectionBaseChange
public import FLT.Mazur.CartesianStructureSections
public import Mathlib.RingTheory.TensorProduct.Basic

/-!
# Flat base change of the ring of global functions

The module comparison for the structure sheaf is the multiplicative tensor
comparison. Thus a quasi-compact separated scheme has the expected ring of
functions after flat affine base change, without assuming it is affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry TensorProduct
open Scheme.Modules
namespace FLT.Mazur.FlatGlobalFunctionBaseChange
open FCurve OpenModuleSectionScalars
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme.{0}}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g)

/-- Section scalars always use the indicated geometric structural map. -/
abbrev sectionAlgebra {Y Z : Scheme} (a : Y ⟶ Z) : Algebra Γ(Z, ⊤) Γ(Y, ⊤) :=
  a.appTop.hom.toAlgebra

/-- Pullback from the original source is linear over the unchanged base. -/
def sourceMap :
    let _ := sectionAlgebra f
    let _ := sectionAlgebra (q ≫ g)
    Γ(X, ⊤) →ₐ[Γ(S, ⊤)] Γ(P, ⊤) := by
  let _ := sectionAlgebra f
  let _ := sectionAlgebra (q ≫ g)
  exact ⟨p.appTop.hom, fun a ↦ by
    change p.appTop (f.appTop a) = (q ≫ g).appTop a
    rw [← h.w, Scheme.Hom.comp_appTop]
    rfl⟩

/-- The canonical multiplicative comparison to actual functions on the pullback. -/
def comparison :
    let _ := sectionAlgebra f
    let _ := sectionAlgebra g
    let _ := sectionAlgebra q
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(X, ⊤) →ₐ[Γ(T, ⊤)] Γ(P, ⊤) := by
  let _ := sectionAlgebra f
  let _ := sectionAlgebra g
  let _ := sectionAlgebra q
  let _ := sectionAlgebra (q ≫ g)
  let _ : IsScalarTower Γ(S, ⊤) Γ(T, ⊤) Γ(P, ⊤) :=
    IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  exact AlgHom.liftEquiv _ _ _ _ (sourceMap h)

/-- The comparison uses the actual two geometric projection maps. -/
theorem comparison_tmul (b : Γ(T, ⊤)) (a : Γ(X, ⊤)) :
    let _ := sectionAlgebra f
    let _ := sectionAlgebra g
    comparison h (b ⊗ₜ[Γ(S, ⊤)] a) = q.appTop b * p.appTop a := rfl

/-- The module action on top-open structure sections is the global section algebra. -/
def topSectionsEquiv :
    let _ := sectionAlgebra f
    Γ(X, ⊤) ≃ₗ[Γ(S, ⊤)] openSections f (structureModule X) ⊤ := by
  let _ := sectionAlgebra f
  refine { Equiv.refl _ with map_add' := fun _ _ ↦ rfl, map_smul' := ?_ }
  intro r a
  change f.appTop r * a = X.presheaf.map (homOfLE le_rfl).op (f.appTop r) * a
  rw [show (homOfLE le_rfl : (⊤ : X.Opens) ⟶ ⊤) = 𝟙 _ from rfl,
    op_id, X.presheaf.map_id]
  rfl

/-- The ring comparison agrees with the sheaf-theoretic module comparison. -/
theorem comparison_eq_structure :
    let _ := sectionAlgebra f
    let _ := sectionAlgebra g
    ∀ x : Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(X, ⊤), comparison h x =
      CartesianStructureSections.comparison h ⊤
        ((topSectionsEquiv (f := f)).lTensor Γ(T, ⊤) x) := by
  let _ := sectionAlgebra f
  let _ := sectionAlgebra g
  dsimp only
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul b a =>
    simp only [LinearEquiv.lTensor_tmul, comparison_tmul]
    rw [CartesianStructureSections.comparison_tmul]
    simp [topSectionsEquiv, Scheme.Hom.appTop,
      show (⊤ : P.Opens).leTop = 𝟙 _ from rfl]
  | add x y hx hy => simp only [map_add, hx, hy]

variable [CompactSpace X] [X.IsSeparated] [IsAffine T] [IsAffine S] [Flat g]

/-- Flat affine base change gives all global functions, with no affineness of the source. -/
theorem comparison_bijective :
    let _ := sectionAlgebra f
    let _ := sectionAlgebra g
    Function.Bijective (comparison h) := by
  let _ := sectionAlgebra f
  let _ := sectionAlgebra g
  let _ : (structureModule X).IsFinitePresentation := unitSheaf_isFinitePresentation X
  let _ := FlatGlobalSectionBaseChange.comparison_isIso h (structureModule X)
  have hb := (ConcreteCategory.bijective_of_isIso
    ((modulePullbackUnitIso p).hom.app (p ⁻¹ᵁ (⊤ : X.Opens)))).comp
      (ConcreteCategory.bijective_of_isIso
        (CartesianOpenSectionMap.comparison h (structureModule X) ⊤))
  convert hb.comp ((topSectionsEquiv (f := f)).lTensor Γ(T, ⊤)).bijective using 1
  funext x
  exact comparison_eq_structure h x

/-- The tensor ring is the actual ring of functions on the geometric base change. -/
def sectionsEquiv :
    let _ := sectionAlgebra f
    let _ := sectionAlgebra g
    let _ := sectionAlgebra q
    Γ(T, ⊤) ⊗[Γ(S, ⊤)] Γ(X, ⊤) ≃ₐ[Γ(T, ⊤)] Γ(P, ⊤) := by
  let _ := sectionAlgebra f
  let _ := sectionAlgebra g
  let _ := sectionAlgebra q
  exact AlgEquiv.ofBijective (comparison h) (comparison_bijective h)

/-- The algebra equivalence retains the original pure tensor formula. -/
theorem sectionsEquiv_tmul (b : Γ(T, ⊤)) (a : Γ(X, ⊤)) :
    let _ := sectionAlgebra f
    let _ := sectionAlgebra g
    sectionsEquiv h (b ⊗ₜ[Γ(S, ⊤)] a) = q.appTop b * p.appTop a := rfl

end FLT.Mazur.FlatGlobalFunctionBaseChange
