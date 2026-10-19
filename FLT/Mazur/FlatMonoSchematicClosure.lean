/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.ChowSourceClosure

/-!
# Recovering a closed subscheme after taking closure along a flat monomorphism

A closed subscheme of a flat monomorphic base extension is recovered by pulling
back its schematic closure. This includes generic fibers of integral models.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FlatMonoSchematicClosure

set_option backward.isDefEq.respectTransparency false

universe u
variable {H U X : Scheme.{u}} (i : H ⟶ U) (b : U ⟶ X)

/-- The canonical map into the pullback of the actual schematic closure. -/
def comparison : H ⟶ pullback (i ≫ b).imageι b :=
  pullback.lift (i ≫ b).toImage i (i ≫ b).toImage_imageι

/-- The comparison retains the original map to the schematic closure. -/
@[reassoc (attr := simp)] theorem comparison_fst :
    comparison i b ≫ pullback.fst _ _ = (i ≫ b).toImage := pullback.lift_fst _ _ _

/-- The comparison retains the original embedded subscheme. -/
@[reassoc (attr := simp)] theorem comparison_snd :
    comparison i b ≫ pullback.snd _ _ = i := pullback.lift_snd _ _ _

variable [IsClosedImmersion i] [Flat b] [Mono b] [QuasiCompact b]

/-- Closedness is inherited from the original closed inclusion. -/
instance comparison_closed : IsClosedImmersion (comparison i b) := by
  let _ : IsClosedImmersion (comparison i b ≫ pullback.snd (i ≫ b).imageι b) := by
    rw [comparison_snd]
    infer_instance
  exact IsClosedImmersion.of_comp_isClosedImmersion (comparison i b) (pullback.snd (i ≫ b).imageι b)

omit [IsClosedImmersion i] [Flat b] [QuasiCompact b] in
/-- The comparison is a flat base change of the dense map to the closure. -/
theorem comparison_isPullback :
    IsPullback (𝟙 H) (comparison i b) (i ≫ b).toImage
      (pullback.fst (i ≫ b).imageι b) :=
  IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp, comparison_fst]⟩

/-- Schematic density survives the flat projection from the generic pullback. -/
instance comparison_dense : IsSchemeTheoreticallyDominant (comparison i b) := by
  let _ := Chow.toImage_schemeTheoreticallyDominant (i ≫ b)
  exact IsSchemeTheoreticallyDominant.of_isPullback (comparison_isPullback i b)

/-- The original closed subscheme is exactly the base change of its closure. -/
instance comparison_isIso : IsIso (comparison i b) :=
  IsClosedImmersion.isIso_iff_ker_eq_bot.mpr (comparison i b).ker_eq_bot

/-- Taking schematic closure along a flat monomorphism loses no generic scheme structure. -/
theorem closure_isPullback : IsPullback (i ≫ b).toImage i (i ≫ b).imageι b := by
  exact IsPullback.of_iso_pullback ⟨(i ≫ b).toImage_imageι⟩
    (asIso (comparison i b)) (comparison_fst i b) (comparison_snd i b)

end FLT.Mazur.FlatMonoSchematicClosure
