/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafGluing

/-!
# Maps into a glued module sheaf

Compatible maps to all chart pushforwards define a unique map into the sheaf of
compatible families. Its components are the entire original chart maps.
-/

@[expose] public noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
namespace FLT.Mazur.ModuleSheafGluing.Data
open ModuleSheafMorphismGluing
universe u
variable {X : Scheme.{u}} {ι : Type u} {U : ι → X.Opens} (D : ModuleSheafGluing.Data U)
variable {S : X.Modules} (a : ∀ i, S ⟶ D.chart i)
variable (ha : ∀ i j, (a i).over (U i ⊓ U j) ≫ (D.transition i j).hom =
  (a j).over (U i ⊓ U j))

/-- A compatible collection of original maps gives a compatible family of sections. -/
def liftFamily (W : X.Opens) (s : Γ(S, W)) : D.families W :=
  ⟨fun i ↦ (a i).app W s, by
    intro i j V hV hi hj
    have hn (k : ι) : res (D.chart k) hV ((a k).app W s) =
        (a k).app V (res S hV s) :=
      (congrArg (fun f ↦ f s) ((a k).mapPresheaf.naturality (homOfLE hV).op)).symm
    rw [hn i, hn j]
    exact congrArg (fun f ↦ localApp f (le_inf hi hj) (res S hV s)) (ha i j)⟩

/-- The map into the glued sheaf retains every chart component. -/
def lift : S ⟶ D.glued :=
  ⟨PresheafOfModules.homMk
    { app := fun W ↦ AddCommGrpCat.ofHom
        { toFun := D.liftFamily a ha W.unop
          map_zero' := by
            apply Subtype.ext
            funext i
            exact map_zero _
          map_add' := fun s t ↦ by
            apply Subtype.ext
            funext i
            exact map_add _ _ _ }
      naturality := fun V W f ↦ by
        ext s
        apply Subtype.ext
        funext i
        exact congrArg (fun g ↦ g s) ((a i).mapPresheaf.naturality f) }
    (fun W r s ↦ by
      apply Subtype.ext
      funext i
      exact (a i).app_smul r s)⟩

/-- Projection of the glued lift is exactly the supplied full original chart map. -/
@[reassoc] theorem lift_projection (i : ι) : D.lift a ha ≫ D.projection i = a i := by
  apply Scheme.Modules.hom_ext
  intro W
  rfl

/-- All chart components jointly determine a morphism into the actual glued object. -/
theorem hom_ext_into_glued {s t : S ⟶ D.glued}
    (h : ∀ i, s ≫ D.projection i = t ≫ D.projection i) : s = t := by
  apply Scheme.Modules.hom_ext
  intro W
  ext x
  apply Subtype.ext
  funext i
  exact congrArg (fun f ↦ f.app W x) (h i)

include ha in
/-- The compatible chart maps have a unique lift into the sheaf of compatible families. -/
theorem existsUnique_lift : ∃! s : S ⟶ D.glued, ∀ i, s ≫ D.projection i = a i := by
  refine ⟨D.lift a ha, D.lift_projection a ha, ?_⟩
  intro t ht
  exact D.hom_ext_into_glued (fun i ↦ (ht i).trans (D.lift_projection a ha i).symm)

end FLT.Mazur.ModuleSheafGluing.Data
