/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedGroupIdealProductBaseChange
public import FLT.Mazur.IdealModuleEquationSquare

/-!
# Sheaf-level base change of the full multiplication equation

The equation comparison retains the actual ideal-module pullback map, not
only a criterion for vanishing or a comparison of geometric points.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
open scoped CategoryTheory.Obj
universe u
namespace FLT.Mazur.ClosedGroupIdeal
open FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S T : Scheme.{u}} (G : Over S) [CommGrpObj G]
  (I : G.left.IdealSheafData) (g : T ⟶ S)
  (J : ((Over.pullback g).obj G).left.IdealSheafData)
  (h : I.comap (pullback.fst G.hom g) = J)

/-- Compare the equation domains using the actual square and pulled ideal inclusion. -/
def multiplicationEquationBaseChangeSource :
    (Scheme.Modules.pullback (productBaseChangeMap G I g J h)).obj
        ((Scheme.Modules.pullback (productMap G I).left).obj (idealModule I)) ⟶
      (Scheme.Modules.pullback (productMap ((Over.pullback g).obj G) J).left).obj
        (idealModule J) :=
  (idealEquationSquareIso I (productMap G I).left
    (productMap ((Over.pullback g).obj G) J).left (productBaseChangeMap G I g J h)
    (pullback.fst G.hom g) (productBaseChangeMap_multiplication G I g J h)).hom ≫
      (Scheme.Modules.pullback (productMap ((Over.pullback g).obj G) J).left).map
        (idealModulePullbackHom I (pullback.fst G.hom g) ≫
          eqToHom (congrArg idealModule h))

/-- The full multiplication module map commutes with arbitrary parameter change. -/
theorem multiplicationEquation_baseChange :
    (Scheme.Modules.pullback (productBaseChangeMap G I g J h)).map
        (multiplicationEquation G I) ≫
          (modulePullbackUnitIso (productBaseChangeMap G I g J h)).hom =
      multiplicationEquationBaseChangeSource G I g J h ≫
        multiplicationEquation ((Over.pullback g).obj G) J := by
  subst J
  simpa only [multiplicationEquationBaseChangeSource, eqToHom_refl, Category.comp_id,
    multiplicationEquation, Category.assoc] using
    idealModulePullbackι_square I (productMap G I).left
      (productMap ((Over.pullback g).obj G) _).left (productBaseChangeMap G I g _ rfl)
      (pullback.fst G.hom g) (productBaseChangeMap_multiplication G I g _ rfl)

/-- The source comparison is invertible whenever the original ideal module pulls back exactly. -/
instance multiplicationEquationBaseChangeSource_isIso
    [IsIso (idealModulePullbackHom I (pullback.fst G.hom g))] :
    IsIso (multiplicationEquationBaseChangeSource G I g J h) := by
  unfold multiplicationEquationBaseChangeSource
  infer_instance

/-- The full obstruction image ideal also commutes with arbitrary base change. -/
theorem multiplicationImage_baseChange :
    J.comap (productMap ((Over.pullback g).obj G) J).left =
      (I.comap (productMap G I).left).comap (productBaseChangeMap G I g J h) := by
  subst J
  exact (idealEquationImage_square I (productMap G I).left
    (productMap ((Over.pullback g).obj G) _).left (productBaseChangeMap G I g _ rfl)
    (pullback.fst G.hom g) (productBaseChangeMap_multiplication G I g _ rfl)).symm

end FLT.Mazur.ClosedGroupIdeal
