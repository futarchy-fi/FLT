/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Full comparison lifts from their exact scalar kernels

On an affine coefficient test, a closed monic comparison has a unique lift
exactly when its scalar kernel is zero. This keeps the entire coefficient
ring, so vanishing merely after reduction does not suffice.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeClosedScalarKernelLift
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D Y B : Scheme.{0}} [IsAffine B] (c : D ⟶ Y) [Mono c] (t : B ⟶ Y)
  [IsClosedImmersion (pullback.snd c t)]

/-- An exact scalar kernel detects a unique arrow on the whole affine test. -/
theorem existsUnique_lift_iff :
    (∃! d : B ⟶ D, d ≫ c = t) ↔ RingHom.ker (pullback.snd c t).appTop.hom = ⊥ := by
  constructor
  · rintro ⟨d, hd, _⟩
    let l := pullback.lift d (𝟙 B) (hd.trans (Category.id_comp t).symm)
    have hl : l ≫ pullback.snd c t = 𝟙 B := pullback.lift_snd _ _ _
    have hk : (pullback.snd c t).ker = ⊥ := by
      apply le_bot_iff.mp
      have h := l.le_ker_comp (pullback.snd c t)
      simpa only [hl, Scheme.Hom.ker_eq_bot_of_isIso] using h
    have he := congrArg (fun K : B.IdealSheafData ↦ K.ideal ⟨⊤, isAffineOpen_top B⟩) hk
    simpa only [Scheme.Hom.ker_apply, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply] using he
  · intro hk
    let _ : IsIso (pullback.snd c t) :=
      IsClosedImmersion.isIso_of_injective_of_isAffine
        ((RingHom.injective_iff_ker_eq_bot _).mpr hk)
    refine ⟨inv (pullback.snd c t) ≫ pullback.fst c t, ?_, ?_⟩
    · change (inv (pullback.snd c t) ≫ pullback.fst c t) ≫ c = t
      rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]
    · intro d hd
      apply (cancel_mono c).mp
      rw [hd, Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]

end FLT.Mazur.SchemeClosedScalarKernelLift
