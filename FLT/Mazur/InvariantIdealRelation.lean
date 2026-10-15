/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# Restricting a relation to an invariant ideal

Exact invariance of an ideal, without a radical hypothesis, constructs both
Cartesian endpoint squares on its closed subscheme. This applies to the full
infinitesimal boundary neighborhoods as well as to the boundary itself.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.InvariantIdealRelation
set_option backward.isDefEq.respectTransparency false
variable {X D : Scheme.{u}} (I : X.IdealSheafData) (p q : D ⟶ X)
  (h : I.comap p = I.comap q)
local notation "j" => I.subschemeι

private theorem eq_subscheme_ι {Z : Scheme.{u}} (J K : Z.IdealSheafData) (e : J = K) :
    (eqToIso (congrArg Scheme.IdealSheafData.subscheme e)).hom ≫ K.subschemeι =
      J.subschemeι := by
  subst e
  simp

/-- The two whole closed pullbacks agree over the original relation scheme. -/
def pullbackIso : pullback p j ≅ pullback q j :=
  (I.comapIso p).symm ≪≫
    eqToIso (congrArg Scheme.IdealSheafData.subscheme h) ≪≫ I.comapIso q

/-- The closed comparison preserves the full original relation arrow. -/
@[reassoc]
theorem pullbackIso_fst : (pullbackIso I p q h).hom ≫ pullback.fst q j =
    pullback.fst p j := by
  dsimp only [pullbackIso, Iso.trans_hom, Iso.symm_hom]
  rw [Category.assoc, Category.assoc, Scheme.IdealSheafData.comapIso_hom_fst,
    eq_subscheme_ι _ _ h, Scheme.IdealSheafData.comapIso_inv_subschemeι]

/-- The independent second endpoint on the entire first-endpoint restriction. -/
def snd : pullback p j ⟶ I.subscheme :=
  (pullbackIso I p q h).hom ≫ pullback.snd q j

/-- The second endpoint is the restriction of the original second endpoint. -/
@[reassoc]
theorem snd_ι : snd I p q h ≫ j = pullback.fst p j ≫ q := by
  rw [snd, Category.assoc, ← pullback.condition, ← Category.assoc, pullbackIso_fst]

/-- Both endpoints restrict along the same actual closed subscheme. -/
theorem snd_isPullback : IsPullback (pullback.fst p j) (snd I p q h) q j :=
  IsPullback.of_iso_pullback ⟨(snd_ι I p q h).symm⟩
    (pullbackIso I p q h) (pullbackIso_fst I p q h) rfl

/-- Etaleness survives restriction with the entire ideal, including nilpotents. -/
instance snd_etale [Etale q] : Etale (snd I p q h) :=
  MorphismProperty.of_isPullback (snd_isPullback I p q h) (inferInstanceAs (Etale q))

/-- Every specified second closed endpoint is automatically retained by the first lift. -/
theorem lift_snd {T : Scheme.{u}} (z : T ⟶ D) (a b : T ⟶ I.subscheme)
    (ha : z ≫ p = a ≫ j) (hb : z ≫ q = b ≫ j) :
    pullback.lift z a ha ≫ snd I p q h = b := by
  apply (cancel_mono j).mp
  rw [Category.assoc, snd_ι, pullback.lift_fst_assoc, hb]

/-- There is exactly one closed arrow retaining the original arrow and both endpoints. -/
theorem lift_existsUnique {T : Scheme.{u}} (z : T ⟶ D) (a b : T ⟶ I.subscheme)
    (ha : z ≫ p = a ≫ j) (hb : z ≫ q = b ≫ j) :
    ∃! w : T ⟶ pullback p j, w ≫ pullback.fst p j = z ∧
      w ≫ pullback.snd p j = a ∧ w ≫ snd I p q h = b := by
  refine ⟨pullback.lift z a ha, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _,
    lift_snd I p q h z a b ha hb⟩, ?_⟩
  intro w hw
  exact pullback.hom_ext (hw.1.trans (pullback.lift_fst _ _ _).symm)
    (hw.2.1.trans (pullback.lift_snd _ _ _).symm)

end FLT.Mazur.InvariantIdealRelation
