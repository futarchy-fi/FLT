/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonPinchingDiagram
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
/-!
# Global sections of scheme coproducts

The Gamma-Spec adjunction turns coproducts into products. The comparison maps
are the actual restrictions, including coproducts formed over a base scheme.
-/

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
@[expose] public noncomputable section
universe u v
namespace FLT.Mazur.SchemeCoproductSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {ι : Type v}
/-- The ring product cone with an index universe independent of its rings. -/
def piFan (R : ι → CommRingCat.{max u v}) : Fan R :=
  Fan.mk (CommRingCat.of (∀ i, R i)) (fun i ↦ CommRingCat.ofHom (Pi.evalRingHom _ i))
/-- The ring of coordinate functions has the product universal property. -/
def piFanIsLimit (R : ι → CommRingCat.{max u v}) : IsLimit (piFan R) where
  lift s := CommRingCat.ofHom <| RingHom.pi fun i ↦ (s.π.app ⟨i⟩).hom
  fac s i := by rfl
  uniq _ _ h := CommRingCat.hom_ext <| DFunLike.ext _ _ fun x ↦ funext fun i ↦
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom <| h ⟨i⟩) x
/-- The categorical product identifies with the ring of coordinate functions. -/
def piIso (R : ι → CommRingCat.{max u v}) : ∏ᶜ R ≅ CommRingCat.of (∀ i, R i) :=
  limit.isoLimitCone ⟨_, piFanIsLimit R⟩
variable (X : ι → Scheme.{max u v})
/-- Global sections send a scheme coproduct to the product of its section rings. -/
def iso : Γ(∐ X, ⊤) ≅ CommRingCat.of (∀ i, Γ(X i, ⊤)) :=
  Scheme.Γ.mapIso (opCoproductIsoProduct X) ≪≫
    PreservesProduct.iso Scheme.Γ (fun i ↦ op (X i)) ≪≫
    piIso (fun i ↦ Γ(X i, ⊤))
theorem iso_apply (r : Γ(∐ X, ⊤)) (i : ι) :
    (iso X).hom r i = (Sigma.ι X i).appTop r := by
  have he : (iso X).hom ≫ CommRingCat.ofHom (Pi.evalRingHom _ i) =
      (Sigma.ι X i).appTop := by
    change Scheme.Γ.map (opCoproductIsoProduct X).hom ≫
      (PreservesProduct.iso Scheme.Γ (fun i ↦ op (X i))).hom ≫
      (piIso (fun i ↦ Γ(X i, ⊤))).hom ≫
      (piFan (fun i ↦ Γ(X i, ⊤))).π.app ⟨i⟩ = _
    rw [piIso, limit.isoLimitCone_hom_π,
      PreservesProduct.iso_hom]
    erw [piComparison_comp_π]
    rw [← Functor.map_comp]
    congr 1
    rw [← Iso.eq_inv_comp]
    exact (opCoproductIsoProduct_inv_comp_ι X i).symm
  exact congrArg (fun f ↦ f.hom r) he
end FLT.Mazur.SchemeCoproductSections
namespace FLT.Mazur.SchemeCoproductSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {ι : Type v} {S : Scheme.{max u v}} (X : ι → Over S)
/-- The same section comparison for the specified coproduct in schemes over a base. -/
def overIso : Γ((∐ X).left, ⊤) ≅ CommRingCat.of (∀ i, Γ((X i).left, ⊤)) :=
  Scheme.Γ.mapIso (asIso (sigmaComparison (Over.forget S) X)).op ≪≫
    iso (fun i ↦ (X i).left)
theorem overIso_apply (r : Γ((∐ X).left, ⊤)) (i : ι) :
    (overIso X).hom r i = (Sigma.ι X i).left.appTop r := by
  rw [show (overIso X).hom r i = (iso (fun i ↦ (X i).left)).hom
    ((sigmaComparison (Over.forget S) X).appTop r) i from rfl, iso_apply]
  have he := ι_comp_sigmaComparison (Over.forget S) X i
  exact congrArg (fun f ↦ f.appTop r) he
end FLT.Mazur.SchemeCoproductSections
