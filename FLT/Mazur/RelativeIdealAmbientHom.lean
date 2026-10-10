/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeIdealFamilyIsomorphism

/-!
# Ambient morphisms on intrinsic relative ideal spaces

Every morphism of original ambients over the coefficient base induces a
morphism of actual scheme pullbacks. Identity, composition, ambient
isomorphism comparison, and cartesianness are proved from the projections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.ClosedIdealCover

variable {A B C S X : Scheme.{u}} (a : A ⟶ S) (b : B ⟶ S) (c : C ⟶ S)
variable (i : A ⟶ B) (hi : i ≫ b = a) (s : X ⟶ S)

/-- Base change of an actual ambient morphism over the fixed coefficient scheme. -/
def relativeIdealAmbientHom : pullback s a ⟶ pullback s b :=
  pullback.lift (pullback.fst _ _) (pullback.snd _ _ ≫ i) (by
    rw [Category.assoc, hi]
    exact pullback.condition)

/-- The induced ambient morphism retains its projection to the test scheme. -/
@[reassoc]
theorem relativeIdealAmbientHom_fst :
    relativeIdealAmbientHom a b i hi s ≫ pullback.fst _ _ = pullback.fst _ _ :=
  pullback.lift_fst _ _ _

/-- The induced ambient morphism acts by the original morphism on ambient projections. -/
@[reassoc]
theorem relativeIdealAmbientHom_snd :
    relativeIdealAmbientHom a b i hi s ≫ pullback.snd _ _ = pullback.snd _ _ ≫ i :=
  pullback.lift_snd _ _ _

/-- The induced square over the original ambient morphism is cartesian. -/
theorem relativeIdealAmbientHom_isPullback :
    IsPullback (relativeIdealAmbientHom a b i hi s) (pullback.snd _ _) (pullback.snd _ _) i := by
  have h : IsPullback (relativeIdealAmbientHom a b i hi s ≫ pullback.fst _ _)
      (pullback.snd s a) s (i ≫ b) := by
    rw [relativeIdealAmbientHom_fst, hi]
    exact IsPullback.of_hasPullback _ _
  exact h.of_right (relativeIdealAmbientHom_snd a b i hi s)
    (IsPullback.of_hasPullback _ _)

instance [IsOpenImmersion i] : IsOpenImmersion (relativeIdealAmbientHom a b i hi s) :=
  MorphismProperty.of_isPullback (relativeIdealAmbientHom_isPullback a b i hi s).flip
    (inferInstance : IsOpenImmersion i)

/-- Ambient identity induces the identity on the actual relative ambient. -/
theorem relativeIdealAmbientHom_id :
    relativeIdealAmbientHom a a (𝟙 A) (Category.id_comp a) s = 𝟙 _ := by
  apply pullback.hom_ext <;>
    simp only [relativeIdealAmbientHom_fst, relativeIdealAmbientHom_snd,
      Category.id_comp, Category.comp_id]

/-- Composed ambient morphisms induce composed relative ambient morphisms. -/
theorem relativeIdealAmbientHom_comp (j : B ⟶ C) (hj : j ≫ c = b) :
    relativeIdealAmbientHom a b i hi s ≫ relativeIdealAmbientHom b c j hj s =
      relativeIdealAmbientHom a c (i ≫ j)
        ((Category.assoc _ _ _).trans ((congrArg (i ≫ ·) hj).trans hi)) s := by
  apply pullback.hom_ext <;>
    simp only [Category.assoc, relativeIdealAmbientHom_fst, relativeIdealAmbientHom_snd,
      relativeIdealAmbientHom_snd_assoc]

/-- The relative morphism induced by an isomorphism is the previously constructed comparison. -/
theorem relativeIdealAmbientHom_iso (e : A ≅ B) (he : e.hom ≫ b = a) :
    relativeIdealAmbientHom a b e.hom he s = (relativeIdealAmbientIso e a b he s).hom := rfl

end FLT.Mazur.ClosedIdealCover
