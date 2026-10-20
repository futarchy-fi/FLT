/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteCharacterAdicChartExt
public import FLT.Mazur.WeierstrassDiagonalizableDefect

/-!
# Detecting the original smooth identity by finite character reductions

The zero section lies in the original infinity chart. The Jacobson open
criterion and adic coordinate separatedness therefore detect equality to
that section in the full original smooth group, without any discriminant
or etaleness assumption.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry MonObj

namespace FLT.Mazur.WeierstrassDiagonalizableDefect

open WeierstrassIntegralChart DiagonalizableCobar

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable {R G : Type} [CommRing R] [AddCommMonoid G]
  (I : Ideal R) [IsAdicComplete I R] (W : WeierstrassCurve R)

/-- The actual smooth identity has its original infinity-chart factorization. -/
theorem smoothCharacterOne_inclusion :
    (1 : Points W (AddMonoidAlgebra R G)).left ≫ (integralSmoothOpen W).ι =
      Spec.map (CommRingCat.ofHom (algebraMap R (AddMonoidAlgebra R G))) ≫
        integralCurveZero W := by
  change (Spec.map _ ≫ integralSmoothZero W) ≫ _ = _
  rw [Category.assoc, integralSmoothZero_inclusion]

variable [Finite G]

/-- All original positive-order character restrictions detect the whole smooth identity. -/
theorem eq_one_of_adic_reduction (p : Points W (AddMonoidAlgebra R G))
    (hp : ∀ m, smoothAlgebraReduction W (coefficientReduction R G (I ^ (m + 1))) p = 1) :
    p = 1 := by
  apply Over.OverMorphism.ext
  apply (cancel_mono (integralSmoothOpen W).ι).mp
  symm
  apply FiniteCharacterAdicElements.schemeMap_ext_of_chart I (integralCurveChart W 1)
  · rw [smoothCharacterOne_inclusion, integralCurveZero]
    rintro _ ⟨x, rfl⟩
    exact ⟨_, rfl⟩
  · intro m
    rw [← Category.assoc, ← Category.assoc]
    have h := congrArg Over.Hom.left ((hp m).trans
      (map_one (smoothAlgebraReduction W (coefficientReduction R G (I ^ (m + 1))))).symm)
    exact congrArg (fun q => q ≫ (integralSmoothOpen W).ι) h.symm

end FLT.Mazur.WeierstrassDiagonalizableDefect
