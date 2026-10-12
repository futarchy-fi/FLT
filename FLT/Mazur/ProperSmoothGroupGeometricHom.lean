/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperGroupPointedHom
public import Mathlib.AlgebraicGeometry.Geometrically.Integral
public import FLT.Mazur.GroupSectionBaseChange

/-!
# The actual geometric pullbacks of a relative pointed group map

A pointed map from a proper smooth geometrically integral relative curve
preserves multiplication on every geometric base change. These are the original
pulled-back group laws, not a transported replacement law.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory MonObj
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {S : Scheme} (G Z : Over S) [GrpObj G] [GrpObj Z]
  [IsProper G.hom] [SmoothOfRelativeDimension 1 G.hom] [GeometricallyIntegral G.hom]
  [IsSeparated Z.hom] [LocallyOfFiniteType Z.hom]
  (f : G ⟶ Z) (hf : η[G] ≫ f = η[Z])

include hf

/-- The actual pointed map on each geometric fiber preserves its original multiplication. -/
theorem properSmoothGroup_geometric_isMonHom {K : Type} [Field K] [IsAlgClosed K]
    (g : Spec (.of K) ⟶ S) :
    let _ : GrpObj ((Over.pullback g).obj G) := Functor.grpObjObj
    let _ : GrpObj ((Over.pullback g).obj Z) := Functor.grpObjObj
    IsMonHom ((Over.pullback g).map f) := by
  let F := Over.pullback g
  let G' := F.obj G
  let Z' := F.obj Z
  let _ : GrpObj G' := Functor.grpObjObj
  let _ : GrpObj Z' := Functor.grpObjObj
  let _ : IsProper G'.hom := inferInstanceAs (IsProper (pullback.snd G.hom g))
  let _ : IsSeparated Z'.hom := inferInstanceAs (IsSeparated (pullback.snd Z.hom g))
  let _ : LocallyOfFiniteType Z'.hom :=
    inferInstanceAs (LocallyOfFiniteType (pullback.snd Z.hom g))
  let _ : Smooth G.hom := SmoothOfRelativeDimension.smooth 1 G.hom
  let _ : Smooth G'.hom := inferInstanceAs (Smooth (pullback.snd G.hom g))
  let _ : GeometricallyIntegral G'.hom :=
    inferInstanceAs (GeometricallyIntegral (pullback.snd G.hom g))
  let _ : IsIntegral G'.left := GeometricallyIntegral.isIntegral_of_subsingleton G'.hom
  let _ : IsLocallyNoetherian G'.left := LocallyOfFiniteType.isLocallyNoetherian G'.hom
  let _ : IsIntegral (G' ⊗ G').left :=
    inferInstanceAs (IsIntegral (pullback G'.hom G'.hom : Scheme))
  apply properGroup_isMonHom_of_one G' Z'
  change (Functor.LaxMonoidal.ε F ≫ F.map η[G]) ≫ F.map f =
    Functor.LaxMonoidal.ε F ≫ F.map η[Z]
  rw [Category.assoc, ← Functor.map_comp, hf]

/-- Multiplication compatibility is equality of the original pulled-back relative maps. -/
theorem properSmoothGroup_geometric_mul {K : Type} [Field K] [IsAlgClosed K]
    (g : Spec (.of K) ⟶ S) :
    (Over.pullback g).map (μ[G] ≫ f) =
      (Over.pullback g).map ((f ⊗ₘ f) ≫ μ[Z]) := by
  let F := Over.pullback g
  let _ : GrpObj (F.obj G) := Functor.grpObjObj
  let _ : GrpObj (F.obj Z) := Functor.grpObjObj
  let _ := properSmoothGroup_geometric_isMonHom G Z f hf g
  apply (cancel_epi (Functor.LaxMonoidal.μ F G G)).mp
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc,
    ← Category.assoc, ← Functor.LaxMonoidal.μ_natural]
  have hm := IsMonHom.mul_hom (F.map f)
  change (Functor.LaxMonoidal.μ F G G ≫ F.map μ[G]) ≫ F.map f =
    (F.map f ⊗ₘ F.map f) ≫ (Functor.LaxMonoidal.μ F Z Z ≫ F.map μ[Z]) at hm
  simpa only [Category.assoc] using hm

end FLT.Mazur.FCurve
