/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationEtaleKernelDescent
public import FLT.Mazur.SchemeRelationNestedKernel
public import FLT.Mazur.SchemeEtaleImageQuotient
public import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent

/-!
# An effective model on the actual original image of an etale atlas

The source image is an open of the original parameter scheme. Descent constructs
its quotient map and its full kernel, even when the atlas is not monomorphic.
An etale surjective atlas model gives an etale surjective open-source model.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeRelationEtaleImageModel
open SchemeRelationRestriction
set_option backward.isDefEq.respectTransparency false
variable {S B Q : Scheme.{u}} {D A : Over S} {p q : D ⟶ A}
  (e : CategoryTheory.EquivalenceRelation p q) (k : B ⟶ A.left) [Etale k]
  (v : B ⟶ Q)
  (H : IsPullback (fst p.left q.left k) (snd p.left q.left k) v v)
local notation "U" => SchemeEtaleImageQuotient.image k
local notation "i" => Scheme.Opens.ι U
local notation "b" => SchemeEtaleImageQuotient.projection k
local notation "r" => fst p.left q.left i
local notation "t" => snd p.left q.left i

include e H in
/-- The atlas model is compatible with the actual surjection onto its original image. -/
theorem compatible {Y : Scheme.{u}} (a c : Y ⟶ B) (h : a ≫ b = c ≫ b) :
    a ≫ v = c ≫ v := by
  apply SchemeRelationEtaleCoverDescent.kernel_compatible e k v H.w a c
  simpa only [Category.assoc, SchemeEtaleImageQuotient.projection_ι] using
    congrArg (fun z ↦ z ≫ i) h

/-- The constructed model starts on a genuine OPEN of the original parameter source. -/
def projection : (U).toScheme ⟶ Q := EffectiveEpi.desc b v (compatible e k v H)

@[reassoc]
theorem cover_projection : b ≫ projection e k v H = v := EffectiveEpi.fac b v _

/-- The descended model coequalizes the entire original relation on the open source. -/
theorem condition : r ≫ projection e k v H = t ≫ projection e k v H := by
  apply (cancel_epi (arrow r t b)).mp
  rw [← Category.assoc, ← Category.assoc, arrow_fst, arrow_snd,
    Category.assoc, Category.assoc, cover_projection]
  have h := congrArg (fun z ↦
    SchemeRelationNestedKernel.toOriginal i k b
      (SchemeEtaleImageQuotient.projection_ι k) ≫ z) H.w
  simpa only [← Category.assoc, SchemeRelationNestedKernel.toOriginal_fst,
    SchemeRelationNestedKernel.toOriginal_snd] using h

/-- The original restricted relation remains monomorphic into the descended candidate kernel. -/
theorem comparison_mono : Mono (pullback.lift r t (condition e k v H)) := by
  constructor
  intro Y a c hac
  apply SchemeRelationReanchoring.endpoint_ext e i
  · simpa only [Category.assoc, pullback.lift_fst] using
      congrArg (fun z ↦ z ≫ pullback.fst (projection e k v H) (projection e k v H)) hac
  · simpa only [Category.assoc, pullback.lift_snd] using
      congrArg (fun z ↦ z ≫ pullback.snd (projection e k v H) (projection e k v H)) hac

/-- The FULL original open-source relation is the kernel of the constructed model. -/
theorem isPullback : IsPullback r t (projection e k v H) (projection e k v H) := by
  let _ := comparison_mono e k v H
  apply SchemeRelationEtaleKernelDescent.isPullback r t b (projection e k v H)
    (condition e k v H)
  rw [cover_projection]
  exact SchemeRelationNestedKernel.isPullback e i k b
    (SchemeEtaleImageQuotient.projection_ι k) v H

/-- Surjectivity of the atlas model is retained on its original open image. -/
theorem projection_surjective [Surjective v] : Surjective (projection e k v H) := by
  constructor
  intro y
  obtain ⟨z, hz⟩ := v.surjective y
  exact ⟨b z, (congrArg (fun a ↦ a z) (cover_projection e k v H)).trans hz⟩

/-- Etale model geometry descends using the full original endpoint, without source monicity. -/
theorem projection_etale [Etale p.left] [Etale v] [Surjective v] :
    Etale (projection e k v H) := by
  let _ : Etale r := inferInstanceAs (Etale
    (pullback.fst (pullback.fst p.left i ≫ q.left) i ≫ pullback.snd p.left i))
  let h := (IsPullback.of_hasPullback b r).paste_vert (isPullback e k v H)
  apply MorphismProperty.of_isPullback_of_descendsAlong
    (P := @Etale) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation) h
  · rw [cover_projection]
    exact ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  · infer_instance

/-- The actual original ground map is retained, as a scheme morphism. -/
@[reassoc]
theorem projection_ground (a : Q ⟶ S) (ha : v ≫ a = k ≫ A.hom) :
    projection e k v H ≫ a = i ≫ A.hom := by
  apply (cancel_epi b).mp
  rw [cover_projection_assoc, ha, ← Category.assoc,
    SchemeEtaleImageQuotient.projection_ι]

end FLT.Mazur.SchemeRelationEtaleImageModel
