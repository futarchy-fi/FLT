/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OneGonSmoothCoefficientGroup
public import FLT.Mazur.OverPullbackTowerGroups
public import FLT.Mazur.CharacterSchemeBaseChange

/-!
# Recovery of one-gon smooth groups through coefficient towers

The original intrinsic group is compared with two actual coefficient base
changes. Both the iterated group law and the initial projection are retained.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry
open scoped CategoryTheory.Obj

namespace FLT.Mazur.OneGonSmoothing

open WeierstrassIntegralChart CharacterSchemeBaseChange

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (A B C : Type) [CommRing A] [CommRing B] [CommRing C]
  [Algebra A B] [Algebra B C] [Algebra A C] [IsScalarTower A B C] (t : A)

/-- Coefficient spectra compose by the specified algebra tower. -/
theorem coefficientTower_baseMap : baseMap B C ≫ baseMap A B = baseMap A C := by
  rw [baseMap, baseMap, baseMap, ← Spec.map_comp]
  exact congrArg (fun f => Spec.map (CommRingCat.ofHom f))
    (IsScalarTower.algebraMap_eq A B C).symm

/-- A sealed natural comparison prevents expansion of equality transport of pullback functors. -/
irreducible_def smoothCoefficientTowerFunctorIso :
    Over.pullback (baseMap A C) ≅ Over.pullback (baseMap A B) ⋙ Over.pullback (baseMap B C) :=
  OverPullbackCoherence.towerIso (baseMap A B) (baseMap B C) (baseMap A C)
    (coefficientTower_baseMap A B C)

/-- Its geometric projections retain the initial object over the coefficient base. -/
@[reassoc] theorem smoothCoefficientTowerFunctorIso_fst_fst (X : Over (Spec (.of A))) :
    ((smoothCoefficientTowerFunctorIso A B C).hom.app X).left ≫
      pullback.fst (pullback.snd X.hom (baseMap A B)) (baseMap B C) ≫
        pullback.fst X.hom (baseMap A B) = pullback.fst X.hom (baseMap A C) := by
  rw [smoothCoefficientTowerFunctorIso_def]
  exact OverPullbackCoherence.towerIso_fst_fst _ _ _ _ X

/-- The full group comparison includes the monoidal composition constraint. -/
irreducible_def smoothCoefficientTowerGroupIso :
    integralSmoothGroup (equation (algebraMap A C t)) ≅
      (Over.pullback (baseMap B C)).mapCommGrp.obj
        ((Over.pullback (baseMap A B)).mapCommGrp.obj (integralSmoothGroup (equation t))) :=
  smoothCoefficientGroupIso (S := C) t ≪≫
    (Functor.mapCommGrpNatIso (smoothCoefficientTowerFunctorIso A B C)).app
      (integralSmoothGroup (equation t)) ≪≫
    (Functor.mapCommGrpCompIso (F := Over.pullback (baseMap A B))
      (G := Over.pullback (baseMap B C))).app (integralSmoothGroup (equation t))

/-- The intrinsic group recovers the group after two successive coefficient changes. -/
def smoothCoefficientTowerIso : (integralSmoothGroup (equation (algebraMap A C t))).X ≅
    (Over.pullback (baseMap B C)).obj
      ((Over.pullback (baseMap A B)).obj (integralSmoothGroup (equation t)).X) :=
  (CommGrp.forget (Over (Spec (.of C)))).mapIso (smoothCoefficientTowerGroupIso A B C t)

instance smoothCoefficientTowerIso_isMonHom :
    IsMonHom (smoothCoefficientTowerIso A B C t).hom := by
  change IsMonHom (smoothCoefficientTowerGroupIso A B C t).hom.hom.hom.hom
  infer_instance

/-- The full group comparison retains the actual geometric tower map. -/
theorem smoothCoefficientTowerIso_hom :
    (smoothCoefficientTowerIso A B C t).hom =
      (smoothCoefficientGroupOverIso (S := C) t).hom ≫
        (smoothCoefficientTowerFunctorIso A B C).hom.app (integralSmoothGroup (equation t)).X := by
  unfold smoothCoefficientTowerIso
  rw [smoothCoefficientTowerGroupIso_def]
  change ((smoothCoefficientGroupOverIso (S := C) t).hom ≫
    (smoothCoefficientTowerFunctorIso A B C).hom.app
      (integralSmoothGroup (equation t)).X) ≫ 𝟙 _ = _
  exact Category.comp_id _

/-- The iterated recovery retains exactly the original smooth coefficient projection. -/
@[reassoc] theorem smoothCoefficientTowerIso_fst_fst :
    (smoothCoefficientTowerIso A B C t).hom.left ≫
      pullback.fst (pullback.snd (integralSmoothStructure (equation t)) (baseMap A B))
        (baseMap B C) ≫ pullback.fst (integralSmoothStructure (equation t)) (baseMap A B) =
          smoothCoefficientProjection (S := C) t := by
  rw [smoothCoefficientTowerIso_hom, Over.comp_left, Category.assoc]
  exact (congrArg (fun f => (smoothCoefficientGroupOverIso (S := C) t).hom.left ≫ f)
    (smoothCoefficientTowerFunctorIso_fst_fst A B C (integralSmoothGroup (equation t)).X)).trans
      (smoothCoefficientGroupIso_fst t)

end FLT.Mazur.OneGonSmoothing
