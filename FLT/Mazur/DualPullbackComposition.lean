/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleSheafDualPullback
public import FLT.Mazur.TensorPullbackComposition

/-!
# Composition of canonical dual pullback comparisons

The intrinsic evaluation pairing respects successive geometric pullbacks.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
universe u
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
namespace FLT.Mazur.FCurve
open ModuleSheafTensor ModuleLineBundleTensorPullback
attribute [local irreducible] ModuleSheafTensor.tensor tensorIso
variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (M : Z.Modules)

/-- Pulling the dual comparison and then pairing agrees with the composite pairing. -/
lemma moduleDualPullbackPairing_comp :
    map ((pullback f).map (moduleSheafDualPullbackHom g M)) (𝟙 _) ≫
        moduleDualPullbackPairing f ((pullback g).obj M) =
      map ((pullbackComp f g).hom.app (moduleSheafDual M))
        ((pullbackComp f g).hom.app M) ≫ moduleDualPullbackPairing (f ≫ g) M := by
  rw [← cancel_epi (tensorIso f ((pullback g).obj (moduleSheafDual M))
    ((pullback g).obj M)).hom]
  rw [← cancel_epi ((pullback f).map (tensorIso g (moduleSheafDual M) M).hom)]
  have hn := tensorIso_naturality f (moduleSheafDualPullbackHom g M)
    (𝟙 ((pullback g).obj M))
  rw [CategoryTheory.Functor.map_id] at hn
  simp only [moduleDualPullbackPairing]
  rw [← reassoc_of% hn, Iso.hom_inv_id_assoc]
  rw [← Functor.map_comp_assoc (pullback f)
    (map (moduleSheafDualPullbackHom g M) (𝟙 _)),
    moduleSheafDualPullbackHom_evaluation]
  simp only [moduleDualPullbackPairing, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
    Category.id_comp]
  rw [tensorIso_comp_assoc, Iso.hom_inv_id_assoc]
  rw [modulePullbackUnitIso_comp_hom, ← Category.assoc]
  have hc := (pullbackComp f g).hom.naturality (moduleSheafDualEvaluation M)
  dsimp only [Functor.comp_map] at hc
  rw [hc, Category.assoc]

/-- The canonical dual comparison respects composition of geometric pullbacks. -/
@[reassoc]
lemma moduleSheafDualPullbackHom_comp :
    (pullback f).map (moduleSheafDualPullbackHom g M) ≫
        moduleSheafDualPullbackHom f ((pullback g).obj M) =
      (pullbackComp f g).hom.app (moduleSheafDual M) ≫
        moduleSheafDualPullbackHom (f ≫ g) M ≫
          moduleSheafDualMap ((pullback f).obj ((pullback g).obj M))
            ((pullbackComp f g).hom.app M) := by
  apply moduleSheafDualHom_ext
  rw [← Category.id_comp (𝟙 ((pullback f).obj ((pullback g).obj M))), map_comp,
    Category.assoc, moduleSheafDualPullbackHom_evaluation]
  rw [map_comp, ← Category.id_comp (𝟙 ((pullback f).obj ((pullback g).obj M))),
    map_comp, Category.assoc, Category.assoc,
    moduleSheafDualEvaluation_naturality]
  simp only [← Category.assoc, ← map_comp, Category.comp_id, Category.id_comp]
  rw [show map ((pullbackComp f g).hom.app (moduleSheafDual M) ≫
      moduleSheafDualPullbackHom (f ≫ g) M) ((pullbackComp f g).hom.app M) =
    map ((pullbackComp f g).hom.app (moduleSheafDual M))
      ((pullbackComp f g).hom.app M) ≫
        map (moduleSheafDualPullbackHom (f ≫ g) M) (𝟙 _) by
      rw [← map_comp, Category.comp_id]]
  rw [Category.assoc, moduleSheafDualPullbackHom_evaluation]
  exact moduleDualPullbackPairing_comp f g M

end FLT.Mazur.FCurve
