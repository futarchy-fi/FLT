/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomology
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Equivalence

/-!
# Cohomology transport along scheme isomorphisms

An isomorphism of schemes induces an equivalence of their open-set sites.
The inverse of the resulting additive-sheaf equivalence is restriction along
its forward morphism. Constant integer sheaves correspond under this
equivalence, so the exact adjunction identifies their Ext cohomology groups.
The comparison with restriction of module sheaves retains the underlying
additive sheaves, and gives transport for the actual `ModuleH` groups.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace FLT.Mazur.SchemeCohomologyIso

variable {X Y : Scheme.{u}} (e : X ≅ Y)

/-- The equivalence on opens uses direct image in both directions. -/
def opensEquivalence : X.Opens ≌ Y.Opens where
  functor := e.hom.opensFunctor
  inverse := e.inv.opensFunctor
  unitIso := NatIso.ofComponents (fun U ↦ eqToIso (by
    dsimp
    simp only [← Scheme.Hom.comp_image, e.hom_inv_id, Scheme.Hom.id_image]))
  counitIso := NatIso.ofComponents (fun U ↦ eqToIso (by
    dsimp
    simp only [← Scheme.Hom.comp_image, e.inv_hom_id, Scheme.Hom.id_image]))

/-- Direct image along the isomorphism identifies the open-cover topologies. -/
instance opensDenseSubsite : e.hom.opensFunctor.IsDenseSubsite
    (Opens.grothendieckTopology X) (Opens.grothendieckTopology Y) := by
  let E := opensEquivalence e
  have : E.functor.IsCocontinuous (Opens.grothendieckTopology X)
      (Opens.grothendieckTopology Y) :=
    inferInstanceAs (e.hom.opensFunctor.IsCocontinuous _ _)
  have : E.inverse.IsCocontinuous (Opens.grothendieckTopology Y)
      (Opens.grothendieckTopology X) :=
    inferInstanceAs (e.inv.opensFunctor.IsCocontinuous _ _)
  exact E.isDenseSubsite_functor_of_isCocontinuous _ _

/-- The sheaf equivalence whose inverse is restriction along `e.hom`. -/
def abelianSheafEquivalence :
    Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u} ≌
      Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u} :=
  Functor.IsDenseSubsite.sheafEquiv _ _ e.hom.opensFunctor _

instance abelianSheafInverseAdditive : (abelianSheafEquivalence e).inverse.Additive where
  map_add := by intros; rfl

instance abelianSheafFunctorAdditive : (abelianSheafEquivalence e).functor.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The constant integer sheaf is carried to the constant integer sheaf. -/
def constantIntegerIso :
    (abelianSheafEquivalence e).functor.obj
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ))) ≅
      (constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}).obj
        (AddCommGrpCat.of (ULift.{u} ℤ)) :=
  (equivCommuteConstant _ _ _ e.hom.opensFunctor
    (isTerminalTop (α := X.Opens)) (by
      have h : e.hom.opensFunctor.obj ⊤ = ⊤ := by
        rw [← Scheme.Hom.inv_preimage e]
        exact Opens.map_top _
      rw [h]
      exact isTerminalTop)).app _

section Cohomology

variable [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u})]

/-- Actual Ext-based sheaf cohomology is invariant under the scheme isomorphism. -/
def sheafHEquiv (F : Sheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{u}) (n : ℕ) :
    Sheaf.H F n ≃+ Sheaf.H ((abelianSheafEquivalence e).inverse.obj F) n :=
  (((Abelian.extFunctor n).mapIso (constantIntegerIso e).op).app F).addCommGroupIsoToAddEquiv
    |>.trans (abelianSheafEquivalence e).toAdjunction.extEquiv

end Cohomology

/-- Restriction in the module category commutes with forgetting to additive sheaves. -/
def moduleRestrictionComparison :
    SheafOfModules.toSheaf Y.ringCatSheaf ⋙ (abelianSheafEquivalence e).inverse ≅
      Scheme.Modules.restrictFunctor e.hom ⋙ SheafOfModules.toSheaf X.ringCatSheaf :=
  Iso.refl _

/-- The underlying additive sheaf comparison at a module. -/
def moduleRestrictionIso (M : Y.Modules) :
    (abelianSheafEquivalence e).inverse.obj (FCurve.moduleAbelianSheaf M) ≅
      FCurve.moduleAbelianSheaf (M.restrict e.hom) :=
  (moduleRestrictionComparison e).app M

/-- Restriction along a scheme isomorphism is an equivalence of module categories. -/
def moduleEquivalence : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.restrictFunctor e.hom)
    (Scheme.Modules.restrictFunctor e.inv)
    (Scheme.Modules.restrictFunctorId.symm ≪≫
      (Scheme.Modules.restrictFunctorCongr e.inv_hom_id).symm ≪≫
      Scheme.Modules.restrictFunctorComp e.inv e.hom)
    ((Scheme.Modules.restrictFunctorComp e.hom e.inv).symm ≪≫
      Scheme.Modules.restrictFunctorCongr e.hom_inv_id ≪≫
      Scheme.Modules.restrictFunctorId)

end FLT.Mazur.SchemeCohomologyIso

namespace FLT.Mazur.FCurve

local instance isoTransportHasExt (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :=
  HasExt.standard _

/-- Additive transport of module cohomology through restriction by a scheme isomorphism. -/
def moduleHIsoEquiv {X Y : Scheme.{u}} (e : X ≅ Y) (M : Y.Modules) (n : ℕ) :
    ModuleH M n ≃+ ModuleH (M.restrict e.hom) n :=
  SchemeCohomologyIso.sheafHEquiv e (moduleAbelianSheaf M) n

end FLT.Mazur.FCurve
