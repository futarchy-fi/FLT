/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Functors

/-!
# Injectives and sections under direct image

Inverse image of abelian sheaves is exact. Its right adjoint, direct image,
therefore preserves injective objects. Global sections of a direct image
are the original global sections, naturally in the coefficient sheaf; this
also gives the comparison of degree-zero sheaf cohomology.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace FLT.Mazur.DirectImageInjectives

local instance sheafHasExt (X : TopCat.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) := HasExt.standard _

variable {X Y : TopCat.{u}} (f : X ⟶ Y)

/-- Inverse image of abelian sheaves preserves finite limits. -/
instance pullbackPreservesFiniteLimits :
    PreservesFiniteLimits (TopCat.Sheaf.pullback AddCommGrpCat.{u} f) := by
  unfold TopCat.Sheaf.pullback
  apply Functor.sheafPullbackConstruction.preservesFiniteLimits

/-- Inverse image is additive, as follows from preservation of finite products. -/
instance pullbackAdditive : (TopCat.Sheaf.pullback AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Direct image is additive, as follows from its right adjoint property. -/
instance pushforwardAdditive : (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).Additive :=
  Functor.additive_of_preserves_binary_products _

/-- Inverse image carries every exact short complex to an exact short complex. -/
theorem pullback_exact (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} Y))
    (hS : S.Exact) : (S.map (TopCat.Sheaf.pullback AddCommGrpCat.{u} f)).Exact :=
  ((Functor.exact_tfae _).out 2 4 rfl rfl).mpr ⟨inferInstance, inferInstance⟩ S hS

/-- The right adjoint of exact inverse image preserves injective objects. -/
instance pushforwardPreservesInjectiveObjects :
    (TopCat.Sheaf.pushforward AddCommGrpCat.{u} f).PreservesInjectiveObjects :=
  Functor.preservesInjectiveObjects_of_adjunction_of_preservesMonomorphisms
    (TopCat.Sheaf.pullbackPushforwardAdjunction AddCommGrpCat.{u} f)

/-- Global sections of an abelian sheaf, as an additive-group-valued functor. -/
def sections (X : TopCat.{u}) : TopCat.Sheaf AddCommGrpCat.{u} X ⥤ AddCommGrpCat.{u} :=
  TopCat.Sheaf.forget _ X ⋙ (evaluation (Opens X)ᵒᵖ AddCommGrpCat).obj (op ⊤)

/-- The identity of global sections under direct image, as a natural isomorphism. -/
def sectionsIso : TopCat.Sheaf.pushforward AddCommGrpCat.{u} f ⋙ sections Y ≅ sections X :=
  Iso.refl _

/-- The sections identity commutes with every morphism of coefficient sheaves. -/
@[reassoc]
lemma sectionsIso_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (α : F ⟶ G) :
    (sections Y).map ((TopCat.Sheaf.pushforward AddCommGrpCat f).map α) ≫
        (sectionsIso f).hom.app G =
      (sectionsIso f).hom.app F ≫ (sections X).map α :=
  (sectionsIso f).hom.naturality α

/-- Degree-zero sheaf cohomology is unchanged by direct image. -/
def hZeroEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) :
    Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) 0 ≃+ Sheaf.H.{u + 1} F 0 :=
  (Sheaf.H.equiv₀ ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) isTerminalTop).trans
    (Sheaf.H.equiv₀ F isTerminalTop).symm

/-- The degree-zero comparison is natural in all coefficient morphisms. -/
lemma hZeroEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X} (α : F ⟶ G)
    (x : Sheaf.H.{u + 1} ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) 0) :
    hZeroEquiv f G (Sheaf.H.map ((TopCat.Sheaf.pushforward AddCommGrpCat f).map α) 0 x) =
      Sheaf.H.map α 0 (hZeroEquiv f F x) := by
  exact (congrArg (Sheaf.H.equiv₀ G isTerminalTop).symm
    (Sheaf.H.equiv₀_naturality isTerminalTop
      ((TopCat.Sheaf.pushforward AddCommGrpCat f).map α) x).symm).trans
    (Sheaf.H.equiv₀_symm_naturality isTerminalTop α
      (Sheaf.H.equiv₀ ((TopCat.Sheaf.pushforward AddCommGrpCat f).obj F) isTerminalTop x)).symm

end FLT.Mazur.DirectImageInjectives
