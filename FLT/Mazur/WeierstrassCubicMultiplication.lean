/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicSection
public import FLT.Mazur.ProjectiveTwistingSheafTensor

/-!
# Multiplication by the cubic from O(-3) to the structure sheaf

The constructed O(3) section defines an actual morphism of module sheaves.
Its coefficient on each standard chart is multiplication by the original
local cubic equation. Injectivity and the quotient identification remain
separate from this construction of the morphism and its local formula.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open FLT.Mazur.ProjectiveSpace FLT.Mazur.FCurve
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle FLT.Mazur.FCurve.ModuleSheafTensor

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R : Type} [CommRing R] (W : WeierstrassCurve R)

/-- The local linear operation, keeping the large twisting formulas behind a named map. -/
def cubicMultiplyLinear (V : (space R (Fin 3)).Opens) :
    (twistCocycle R (Fin 3) (-3)).sections V →ₗ[Γ(space R (Fin 3), V)]
      (twistCocycle R (Fin 3) 0).sections V :=
  (twistSectionsMulLinear R (Fin 3) (-3) 3 V).flip (cubicTwistSection W V)

/-- The local linear maps commute with restriction. -/
theorem cubicMultiplyLinear_restrict {V U : (space R (Fin 3)).Opens} (h : U ≤ V)
    (s : (twistCocycle R (Fin 3) (-3)).sections V) :
    cubicMultiplyLinear W U ((twistCocycle R (Fin 3) (-3)).restrict h s) =
      (twistCocycle R (Fin 3) 0).restrict h (cubicMultiplyLinear W V s) := by
  apply Subtype.ext
  funext j
  change res _ (s.val j) * res _ (cubicEquationSection W j) =
    res _ (s.val j * res _ (cubicEquationSection W j))
  rw [map_mul, res_res]

/-- Multiplication by the specified cubic, with target the zero twist. -/
def cubicTwistMultiply : twistingSheaf R (Fin 3) (-3) ⟶ twistingSheaf R (Fin 3) 0 :=
  ⟨{ app V := ModuleCat.ofHom (cubicMultiplyLinear W V.unop)
     naturality {V U} f := by
       apply ModuleCat.hom_ext
       apply LinearMap.ext
       intro s
       exact cubicMultiplyLinear_restrict W (leOfHom f.unop) s }⟩

/-- The resulting morphism O(-3) to the actual structure sheaf of the projective plane. -/
def cubicStructureMultiply :
    twistingSheaf R (Fin 3) (-3) ⟶ structureModule (space R (Fin 3)) :=
  cubicTwistMultiply W ≫ (twistingSheafZeroIso R (Fin 3)).hom

/-- On compatible tuples, multiplication uses exactly the original chart equation. -/
@[simp] theorem cubicTwistMultiply_coordinate (V : (space R (Fin 3)).Opens)
    (s : (twistCocycle R (Fin 3) (-3)).sections V) (j : Fin 3) :
    ((cubicTwistMultiply W).app V s).val j =
      s.val j * res inf_le_right (cubicEquationSection W j) := rfl

/-- The zero-twist isomorphism glues exactly the supplied local functions. -/
theorem cubicZeroTwistIso_coordinate (V : (space R (Fin 3)).Opens)
    (s : (twistCocycle R (Fin 3) 0).sections V) (j : Fin 3) :
    res (X := space R (Fin 3)) inf_le_left
      ((twistingSheafZeroIso R (Fin 3)).hom.app V s) = s.val j := by
  have h := (sectionsCongr (twistingSheafZeroIso R (Fin 3)) V).symm_apply_apply s
  exact congrArg (fun t : (twistCocycle R (Fin 3) 0).sections V => t.val j) h

/-- The structure-valued map is locally multiplication by the genuine cubic equation. -/
theorem cubicStructureMultiply_coordinate (V : (space R (Fin 3)).Opens)
    (s : (twistCocycle R (Fin 3) (-3)).sections V) (j : Fin 3) :
    res (X := space R (Fin 3)) inf_le_left ((cubicStructureMultiply W).app V s) =
      s.val j * res inf_le_right (cubicEquationSection W j) :=
  (cubicZeroTwistIso_coordinate V ((cubicTwistMultiply W).app V s) j).trans
    (cubicTwistMultiply_coordinate W V s j)

end FLT.Mazur.WeierstrassIntegralChart
