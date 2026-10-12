/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GrassmannianSheafQuotientClasses
public import FLT.Mazur.GrassmannianSheafClassificationFaithful
public import FLT.Mazur.GrassmannianSheafClassificationPullback

/-!
# Faithful natural classification of quotient isomorphism classes

Classification descends to actual quotient isomorphism classes. It is injective
and commutes with arbitrary scheme pullback of the whole ambient epimorphism.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GrassmannianChart
universe u
variable {R M ι κ : Type u} [CommRing R] [AddCommGroup M] [Module R M]
  [Fintype ι] [Fintype κ] {d : ℕ}
variable {X : Scheme.{u}} (β : X ⟶ Spec (.of R))
variable (b : Module.Basis ι R M) (hκ : Fintype.card κ = Fintype.card ι - d)

namespace LocallyFreeSheafQuotient
variable (P Q : LocallyFreeSheafQuotient (M := M) β d)

/-- The original full quotient determines a scheme morphism over its original base. -/
def classifyingMorphism : {f : X ⟶ ambientGrassmannianScheme R M κ d //
    f ≫ ambientGrassmannianStructure R M κ d = β} :=
  ⟨locallyFreeQuotientClassifyingMap β P.projection b hκ P.frames (by simp),
    locallyFreeQuotientClassifyingMap_over β P.projection b hκ P.frames (by simp)⟩

/-- The original quotient atlas witnesses classification of this scheme morphism. -/
theorem classifyingMorphism_spec :
    SheafQuotientClassifies β P.projection b hκ (P.classifyingMorphism β b hκ).val :=
  locallyFreeQuotientClassifyingMap_spec β P.projection b hκ P.frames (by simp)

/-- Quotient isomorphism is precisely equality of original classifying scheme maps. -/
theorem classifyingMorphism_eq_iff :
    P.classifyingMorphism β b hκ = Q.classifyingMorphism β b hκ ↔ P.Equivalent Q := by
  rw [Subtype.ext_iff]
  exact locallyFreeQuotientClassifyingMap_eq_iff_iso β P.projection Q.projection b hκ
    P.frames (by simp) Q.frames (by simp)

end LocallyFreeSheafQuotient

/-- Classification of actual sheaf quotient isomorphism classes over the original base. -/
def sheafQuotientClassifying : LocallyFreeSheafQuotientClass (M := M) β d →
    {f : X ⟶ ambientGrassmannianScheme R M κ d //
      f ≫ ambientGrassmannianStructure R M κ d = β} :=
  Quotient.lift (fun P ↦ P.classifyingMorphism β b hκ)
    (fun P Q h ↦ (P.classifyingMorphism_eq_iff β b hκ Q).mpr h)

/-- The constructed classifying map distinguishes all full quotient isomorphism classes. -/
theorem sheafQuotientClassifying_injective :
    Function.Injective (sheafQuotientClassifying β b hκ) := by
  intro P Q
  induction P using Quotient.inductionOn with | h P =>
    induction Q using Quotient.inductionOn with | h Q =>
      intro h
      exact Quotient.sound ((P.classifyingMorphism_eq_iff β b hκ Q).mp h)

/-- Classification on quotient classes commutes with arbitrary scheme pullback. -/
theorem sheafQuotientClassifying_pullback {Y : Scheme.{u}} (g : Y ⟶ X)
    (P : LocallyFreeSheafQuotientClass (M := M) β d) :
    (sheafQuotientClassifying (g ≫ β) b hκ
      (locallyFreeSheafQuotientClassPullback β d g P)).val =
      g ≫ (sheafQuotientClassifying β b hκ P).val := by
  induction P using Quotient.inductionOn with | h P =>
    exact locallyFreeQuotientClassifyingMap_pullback β P.projection b hκ P.frames (by simp) g

end FLT.Mazur.GrassmannianChart
