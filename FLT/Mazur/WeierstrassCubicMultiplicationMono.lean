/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCubicChartRegular
public import FLT.Mazur.WeierstrassCubicMultiplication
public import FLT.Mazur.WeierstrassFlatSectionRegular
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Injectivity of multiplication by the actual cubic

Regularity on affine charts persists on every subopen by localization at
stalks. The coordinate formula for cubic multiplication then proves
injectivity on all sections and hence a monomorphism of module sheaves.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open FLT.Mazur.ProjectiveSpace FLT.Mazur.FCurve
open FLT.Mazur.FCurve.ModuleSheafUnitCocycle

namespace FLT.Mazur.WeierstrassIntegralChart

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local instance] MvPolynomial.gradedAlgebra

/-- Restriction from an affine open preserves regularity, even to a nonaffine open. -/
theorem affineOpen_res_isRegular {X : Scheme} {U V : X.Opens}
    (hU : IsAffineOpen U) (h : V ≤ U) {a : Γ(X, U)} (ha : IsRegular a) :
    IsRegular (res h a) := by
  have hl : IsLeftRegular (res h a) := by
    intro b c he
    apply TopCat.Presheaf.section_ext X.sheaf V b c
    intro x hx
    change X.presheaf.germ V x hx b = X.presheaf.germ V x hx c
    let _ := TopCat.Presheaf.algebra_section_stalk X.presheaf (⟨x, h hx⟩ : U)
    let _ := hU.isLocalization_stalk ⟨x, h hx⟩
    have hr := flatRingHom_isRegular (X.presheaf.germ U x (h hx)).hom
      (RingHom.flat_algebraMap_iff.mpr
        (IsLocalization.flat (X.presheaf.stalk x)
          (hU.primeIdealOf ⟨x, h hx⟩).asIdeal.primeCompl)) ha
    have hh : X.presheaf.germ V x hx (res h a) =
        X.presheaf.germ U x (h hx) a := by
      exact X.presheaf.germ_res_apply (homOfLE h) x hx a
    apply hr.left
    have hg := congrArg (X.presheaf.germ V x hx) he
    simpa only [map_mul, hh] using hg
  exact ⟨hl, fun b c he => hl (by simpa only [mul_comm] using he)⟩

variable {R : Type} [CommRing R] [IsDomain R] (W : WeierstrassCurve R)

/-- The regular function on a standard chart is a non-zero-divisor. -/
theorem cubicEquationSection_regular (j : Fin 3) :
    IsRegular (cubicEquationSection W j) := by
  exact flatRingHom_isRegular
    (Proj.basicOpenIsoAway (grading R (Fin 3)) (MvPolynomial.X j)
      (MvPolynomial.isHomogeneous_X R j) (by decide)).hom.hom
    (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
    (projectiveChartEquation_regular W j)

/-- Every restricted local equation remains regular. -/
theorem cubicEquationSection_restrict_regular (j : Fin 3)
    {V : (space R (Fin 3)).Opens} (h : V ≤ chart R (Fin 3) j) :
    IsRegular (res h (cubicEquationSection W j)) :=
  affineOpen_res_isRegular
    (Proj.isAffineOpen_basicOpen _ _ (MvPolynomial.isHomogeneous_X R j) (by decide))
    h (cubicEquationSection_regular W j)

/-- Multiplication is injective on the actual compatible tuples over every open. -/
theorem cubicTwistMultiply_injective (V : (space R (Fin 3)).Opens) :
    Function.Injective ((cubicTwistMultiply W).app V) := by
  intro s t h
  apply Subtype.ext
  funext j
  apply (cubicEquationSection_restrict_regular W j inf_le_right).right
  exact congrArg (fun z : (twistCocycle R (Fin 3) 0).sections V => z.val j) h

/-- The genuine map of twisting sheaves is a monomorphism over every domain. -/
instance cubicTwistMultiply_mono : Mono (cubicTwistMultiply W) := by
  apply (Scheme.Modules.toPresheafOfModules _).mono_of_mono_map
  exact PresheafOfModules.mono_of_injective (fun {V} => cubicTwistMultiply_injective W V.unop)

/-- The actual structure-valued cubic multiplication is a monomorphism. -/
instance cubicStructureMultiply_mono : Mono (cubicStructureMultiply W) := by
  dsimp only [cubicStructureMultiply]
  infer_instance

end FLT.Mazur.WeierstrassIntegralChart
