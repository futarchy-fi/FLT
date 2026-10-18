/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial

/-!
# Pulling original locally closed equations into a coefficient scheme

When the coefficient map factors through the same monomorphism as the closed
subscheme, its pullback is the subscheme of the pulled-back ideal. This gives
the full scheme identification, rather than an equality of underlying sets.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeMonoIdealPullback
set_option backward.isDefEq.respectTransparency false
variable {X Y Z S : Scheme.{0}} (a : Z ⟶ X) (f : Y ⟶ X) (i : X ⟶ S) [Mono i]

/-- Composing both legs with a mono retains the full pullback scheme. -/
def compMonoIso : pullback a f ≅ pullback (a ≫ i) (f ≫ i) where
  hom := pullback.lift (pullback.fst a f) (pullback.snd a f) (by
    rw [← Category.assoc, pullback.condition, Category.assoc])
  inv := pullback.lift (pullback.fst (a ≫ i) (f ≫ i))
    (pullback.snd (a ≫ i) (f ≫ i))
    ((cancel_mono i).mp (by simp only [Category.assoc]; exact pullback.condition))
  hom_inv_id := by apply pullback.hom_ext <;> simp
  inv_hom_id := by apply pullback.hom_ext <;> simp

/-- The isomorphism preserves all original coefficient coordinates. -/
@[reassoc]
theorem compMonoIso_hom_snd :
    (compMonoIso a f i).hom ≫ pullback.snd (a ≫ i) (f ≫ i) = pullback.snd a f :=
  pullback.lift_snd _ _ _

variable (I : X.IdealSheafData)

/-- The actual coefficient ideal realizes the locally closed base change. -/
def idealPullbackIso :
    (I.comap f).subscheme ≅ pullback (I.subschemeι ≫ i) (f ≫ i) :=
  I.comapIso f ≪≫ pullbackSymmetry f I.subschemeι ≪≫ compMonoIso I.subschemeι f i

/-- The identification is over the complete unchanged coefficient scheme. -/
@[reassoc]
theorem idealPullbackIso_hom_snd :
    (idealPullbackIso f i I).hom ≫ pullback.snd (I.subschemeι ≫ i) (f ≫ i) =
      (I.comap f).subschemeι := by
  simp only [idealPullbackIso, Iso.trans_hom, Category.assoc, compMonoIso_hom_snd,
    pullbackSymmetry_hom_comp_snd, Scheme.IdealSheafData.comapIso_hom_fst]

/-- The full locally closed stage becomes a closed immersion on this coefficient base. -/
instance idealPullback_snd_closed :
    IsClosedImmersion (pullback.snd (I.subschemeι ≫ i) (f ≫ i)) := by
  have he : pullback.snd (I.subschemeι ≫ i) (f ≫ i) =
      (idealPullbackIso f i I).inv ≫ (I.comap f).subschemeι := by
    rw [← idealPullbackIso_hom_snd f i I, Iso.inv_hom_id_assoc]
  rw [he]
  infer_instance

/-- Its kernel is the actual pulled-back ideal, including every nilpotent. -/
theorem idealPullback_snd_kernel :
    (pullback.snd (I.subschemeι ≫ i) (f ≫ i)).ker = I.comap f := by
  rw [← Scheme.Hom.ker_comp_of_isIso (idealPullbackIso f i I).hom,
    idealPullbackIso_hom_snd, Scheme.IdealSheafData.ker_subschemeι]

end FLT.Mazur.SchemeMonoIdealPullback
