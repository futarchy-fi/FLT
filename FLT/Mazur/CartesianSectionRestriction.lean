/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianOpenSectionMap
public import FLT.Mazur.FlatSectionEqualizer

/-!
# Restriction of cartesian section tensors

The canonical comparison commutes with the base-linear restriction maps in the
finite section equalizer, on all tensors.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules TensorProduct
open scoped ChangeOfRings
namespace FLT.Mazur.CartesianSectionRestriction
open Chow OpenModuleSectionScalars CartesianOpenSectionMap
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme}
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  (h : IsPullback p q f g) (M : X.Modules)

/-- Restriction naturality of the actual tensor comparison as a module morphism. -/
lemma comparison_naturality {U V : X.Opens} (i : U ≤ V) :
    (ModuleCat.extendScalars g.appTop.hom).map
        (ModuleCat.ofHom (baseRestriction M f.appTop.hom i)) ≫ comparison h M U =
      comparison h M V ≫ ModuleCat.ofHom
        (X := openSections q ((pullback p).obj M) (p ⁻¹ᵁ V))
        (Y := openSections q ((pullback p).obj M) (p ⁻¹ᵁ U))
        (baseRestriction ((pullback p).obj M) q.appTop.hom
          ((TopologicalSpace.Opens.map p.base).map (homOfLE i)).le) := by
  apply ModuleCat.ExtendScalars.hom_ext
  intro m
  change comparison h M U
    ((ModuleCat.extendScalars g.appTop.hom).map
      (ModuleCat.ofHom (baseRestriction M f.appTop.hom i))
        ((1 : Γ(T, ⊤)) ⊗ₜ[Γ(S, ⊤),g.appTop.hom] m)) = _
  rw [ModuleCat.ExtendScalars.map_tmul]
  exact (comparison_restrict h M (homOfLE i) 1 m).symm

/-- Standard tensor restriction agrees with restriction of the compared section. -/
lemma comparison_lTensor {U V : X.Opens} (i : U ≤ V) :
    letI : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
    ∀ t : Γ(T, ⊤) ⊗[Γ(S, ⊤)] baseSections M f.appTop.hom V,
      comparison h M U
          (AlgebraTensorModule.lTensor Γ(T, ⊤) Γ(T, ⊤)
            (baseRestriction M f.appTop.hom i) t) =
        baseRestriction ((pullback p).obj M) q.appTop.hom
          ((TopologicalSpace.Opens.map p.base).map (homOfLE i)).le
            (comparison h M V t) := by
  let : Algebra Γ(S, ⊤) Γ(T, ⊤) := g.appTop.hom.toAlgebra
  intro t
  induction t using TensorProduct.inductionOn with
  | add a b ha hb => simp only [map_add, ha, hb]
  | tmul b m =>
    exact (comparison_restrict h M (homOfLE i) b m).symm

end FLT.Mazur.CartesianSectionRestriction
