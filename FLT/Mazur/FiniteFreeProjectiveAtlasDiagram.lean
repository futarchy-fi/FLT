/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteFreeProjectiveChartRefinement
public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Equifibered diagrams of actual finite free projective charts

A diagram of affine opens with actual finite free sheaf charts induces a
projective scheme diagram with cartesian projection squares. For a locally
directed base diagram its colimit is a scheme over the original base.
The homogeneous generators use the quotient convention; a section-line bundle
still requires dual chart transitions and the covering atlas construction.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
namespace FLT.Mazur.FiniteFreeProjectiveAtlas
open FiniteFreeChartTransitions ProjectiveSpace
variable {X : Scheme.{u}} (M : X.Modules) {J : Type u} [SmallCategory J]
    (U : J ⥤ X.Opens) [∀ i, IsAffine (U.obj i).toScheme]
    (ι : J → Type u) [∀ i, Finite (ι i)]
    (e : ∀ i, M.restrict (U.obj i).ι ≅ SheafOfModules.free (ι i))

/-- Actual projective charts and their canonical refinement maps form a functor. -/
def diagram : J ⥤ Scheme.{u} where
  obj i := space Γ((U.obj i).toScheme, ⊤) (ι i)
  map {i j} f := chartInclusion M (U.map f).le (e i) (e j)
  map_id i := chartInclusion_self M (e i)
  map_comp f g := (chartInclusion_comp M (U.map f).le (U.map g).le _ _ _).symm

/-- The projections to the original affine opens form a natural transformation. -/
def projection : diagram M U ι e ⟶ U ⋙ X.restrictFunctor ⋙ Over.forget X where
  app i := affineProjection (U.obj i).toScheme (ι i)
  naturality := by
    intro i j f
    exact chartInclusion_projection M (U.map f).le (e i) (e j)

/-- Every square of the projective projection is cartesian. -/
lemma projection_equifibered : (projection M U ι e).Equifibered := by
  intro i j f
  exact chartInclusion_isPullback M (U.map f).le (e i) (e j)

instance diagram_map_isOpenImmersion {i j : J} (f : i ⟶ j) :
    IsOpenImmersion ((diagram M U ι e).map f) := by
  change IsOpenImmersion (chartInclusion M (U.map f).le (e i) (e j))
  infer_instance

variable [Quiver.IsThin J]
    [((U ⋙ X.restrictFunctor ⋙ Over.forget X) ⋙ Scheme.forget).IsLocallyDirected]

instance diagram_isLocallyDirected : ((diagram M U ι e) ⋙ Scheme.forget).IsLocallyDirected :=
  Scheme.isLocallyDirected_of_equifibered_of_injective (projection M U ι e)
    (projection_equifibered M U ι e) (fun _ ↦ Scheme.Hom.injective _)

/-- Glue the actual quotient projective charts in a locally directed affine system. -/
def glued : Scheme.{u} := colimit (diagram M U ι e)

/-- The glued quotient chart system carries its actual projection to the base scheme. -/
def toBase : glued M U ι e ⟶ X :=
  colimit.desc (diagram M U ι e)
    { pt := X
      ι :=
        { app := fun i ↦ affineProjection (U.obj i).toScheme (ι i) ≫ (U.obj i).ι
          naturality := by
            intro i j f
            change chartInclusion M (U.map f).le (e i) (e j) ≫
              (affineProjection (U.obj j).toScheme (ι j) ≫ (U.obj j).ι) =
                (affineProjection (U.obj i).toScheme (ι i) ≫ (U.obj i).ι) ≫ 𝟙 X
            rw [Category.comp_id, ← Category.assoc]
            rw [chartInclusion_projection]
            simp } }

/-- Each actual projective chart recovers its affine-base projection after gluing. -/
@[reassoc (attr := simp)]
lemma chart_toBase (i : J) :
    colimit.ι (diagram M U ι e) i ≫ toBase M U ι e =
      affineProjection (U.obj i).toScheme (ι i) ≫ (U.obj i).ι := by
  exact colimit.ι_desc _ _

/-- The projective charts give an actual open cover of their glued scheme. -/
def cover : (glued M U ι e).OpenCover :=
  Scheme.IsLocallyDirected.openCover (diagram M U ι e)

end FLT.Mazur.FiniteFreeProjectiveAtlas
