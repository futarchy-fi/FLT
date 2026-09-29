/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OpenSheafExtensionExact
public import FLT.Mazur.OpenSheafFreeComparison
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction

/-!
# Cohomology on an open subspace

Exact extension and restriction transport Ext from the ambient free-open sheaf
to Ext from the constant integer sheaf on the open subspace. The resulting
comparison commutes with every coefficient morphism.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TopCat.Presheaf

universe u v

namespace FLT.Mazur.OpenSheafRestriction

variable {X : TopCat.{u}} (W : Opens X)

instance restriction_additive : (restriction W).Additive where
  map_add := by intros; rfl

/-- Restriction preserves exactness, as seen on the unchanged stalks inside the open. -/
lemma restriction_map_exact (S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{u} X))
    (hS : S.Exact) : (S.map (restriction W)).Exact := by
  apply (TopCat.Sheaf.exact_iff_stalkFunctor_map_exact _).mpr
  intro x
  let e : S.map (TopCat.Sheaf.forget AddCommGrpCat.{u} X ⋙
        stalkFunctor AddCommGrpCat.{u} x.val) ≅
      (S.map (restriction W)).map
        (TopCat.Sheaf.forget AddCommGrpCat.{u} (TopCat.of W) ⋙
          stalkFunctor AddCommGrpCat.{u} x) :=
    ShortComplex.isoMk (restrictionPresheafStalkIso W S.X₁.obj x)
      (restrictionPresheafStalkIso W S.X₂.obj x)
      (restrictionPresheafStalkIso W S.X₃.obj x)
      (restrictionPresheafStalkIso_naturality W S.f.hom x).symm
      (restrictionPresheafStalkIso_naturality W S.g.hom x).symm
  exact ShortComplex.exact_of_iso e
    ((TopCat.Sheaf.exact_iff_stalkFunctor_map_exact S).mp hS x.val)

instance restriction_preservesHomology : (restriction W).PreservesHomology :=
  Functor.preservesHomology_of_map_exact _ (restriction_map_exact W)

instance restriction_preservesFiniteColimits : PreservesFiniteColimits (restriction W) :=
  (restriction W).preservesFiniteColimits_of_preservesHomology

end FLT.Mazur.OpenSheafRestriction

namespace FLT.Mazur.OpenSheafCohomology

open OpenSheafRestriction OpenSheafFreeComparison

variable {X : TopCat.{u}} (W : Opens X)
  [HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
  [HasExt.{v} (Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u})]

local instance ambientHasExt : HasExt.{v} (TopCat.Sheaf AddCommGrpCat.{u} X) :=
  inferInstanceAs (HasExt.{v} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}))

local instance openHasExt : HasExt.{v} (TopCat.Sheaf AddCommGrpCat.{u} (TopCat.of W)) :=
  inferInstanceAs (HasExt.{v} (Sheaf (Opens.grothendieckTopology W) AddCommGrpCat.{u}))

/-- Ambient cohomology on an open agrees with cohomology of the restricted sheaf. -/
def openHEquiv (F : TopCat.Sheaf AddCommGrpCat.{u} X) (n : ℕ) :
    F.H' n W ≃+ Sheaf.H ((restriction W).obj F) n :=
  (((Abelian.extFunctor n).mapIso (extensionFreeOpenIso W).op).app F)
    |>.addCommGroupIsoToAddEquiv |>.trans (adjunction W).extEquiv

/-- The comparison is natural in the coefficient sheaf. -/
lemma openHEquiv_naturality {F G : TopCat.Sheaf AddCommGrpCat.{u} X}
    (f : F ⟶ G) (n : ℕ) (x : F.H' n W) :
    openHEquiv W G n
        (((Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) n).map f).app
          (op W) x) =
      Sheaf.H.map ((restriction W).map f) n (openHEquiv W F n x) := by
  change (adjunction W).extEquiv
      ((Abelian.Ext.mk₀ (extensionFreeOpenIso W).hom).comp
        (x.comp (Abelian.Ext.mk₀ f) (add_zero n)) (zero_add n)) = _
  rw [← Abelian.Ext.comp_assoc _ _ _ (zero_add n) (add_zero n) (by omega)]
  exact (adjunction W).extEquiv_naturality_right₀ _ f

end FLT.Mazur.OpenSheafCohomology
