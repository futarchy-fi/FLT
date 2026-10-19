/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassFlatSectionRegular
public import Mathlib.RingTheory.Bezout
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Flatness over a Bezout base from a schematically dense flat source

The injection on sections retains regular scalar multiplication. Over a
Bezout domain this implies flatness of every affine target chart, even
when the dense source is not affine.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.SchematicDenseBezoutFlat
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {X Y S : Scheme} [IsAffine S] [IsDomain Γ(S, ⊤)] [IsBezout Γ(S, ⊤)]
  (f : X ⟶ Y) (g : Y ⟶ S) [QuasiCompact f] [IsSchemeTheoreticallyDominant f]
  [Flat (f ≫ g)]
include f

/-- Affine target sections have no scalar torsion, detected on the dense flat source. -/
theorem affine_flat [IsAffine Y] : Flat g := by
  apply (HasRingHomProperty.iff_of_isAffine (P := @Flat)).mpr
  let _ := g.appTop.hom.toAlgebra
  let _ : Module.IsTorsionFree Γ(S, ⊤) Γ(Y, ⊤) := by
    apply Module.IsTorsionFree.of_smul_eq_zero
    intro a b hab
    by_cases ha : a = 0
    · exact Or.inl ha
    right
    apply (show Function.Injective f.appTop from f.app_injective ⊤)
    have hr := WeierstrassIntegralChart.flat_appTop_isRegular (f ≫ g)
      (IsRegular.of_ne_zero ha)
    apply hr.left
    change g.appTop a * b = 0 at hab
    have he := congrArg (fun b : Γ(Y, ⊤) ↦ f.appTop b) hab
    simpa only [Algebra.smul_def, RingHom.algebraMap_toAlgebra, map_mul,
      Scheme.Hom.comp_appTop, CommRingCat.comp_apply, map_zero, mul_zero] using he
  change Module.Flat Γ(S, ⊤) Γ(Y, ⊤)
  exact Module.Flat.flat_iff_torsion_eq_bot_of_isBezout.mpr
    (Submodule.isTorsionFree_iff_torsion_eq_bot.mp inferInstance)

/-- A quasi-compact schematically dense flat source forces flatness over a Bezout base. -/
theorem flat : Flat g := by
  apply (IsZariskiLocalAtSource.iff_of_openCover Y.affineCover).mpr
  intro i
  let j := Y.affineCover.f i
  let q := pullback.snd f j
  let _ : IsSchemeTheoreticallyDominant q :=
    inferInstanceAs (IsSchemeTheoreticallyDominant (pullback.snd f j))
  let _ : Flat (q ≫ (j ≫ g)) := by
    rw [← Category.assoc, ← pullback.condition, Category.assoc]
    infer_instance
  exact affine_flat q (j ≫ g)

end FLT.Mazur.SchematicDenseBezoutFlat
