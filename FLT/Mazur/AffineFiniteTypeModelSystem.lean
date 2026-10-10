/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FiniteTypeAffineApproximation

/-!
# Finitely presented model systems for actual affine charts

A finite-type morphism from an affine scheme to an affine base has a
cofiltered system of finitely presented affine models over that same base.
Its limit cone has the original scheme as its literal vertex. The transition
maps are closed immersions and every projection commutes with the original
structure morphism. This is the chart construction, before gluing.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u

section

variable (R B : Type u) [CommRing R] [CommRing B] [Algebra R B]
  [Algebra.FiniteType R B]

/-- The structure maps of the affine stages form a natural transformation. -/
def affineStructure : affineDiagram R B ⟶ (Functor.const _).obj (Spec (.of R)) where
  app i := FiniteRelationModel.stageStructure R (relationIdeal R B) i.unop
  naturality i j h := by
    change Spec.map
      (CommRingCat.ofHom
        (FiniteRelationModel.transition R (relationIdeal R B) (leOfHom h.unop)).toRingHom) ≫
      _ = _
    exact FiniteRelationModel.stageStructure_transition R _ (leOfHom h.unop)

/-- Replace the spectrum vertex by an isomorphic original affine chart. -/
def chartCone {X : Scheme.{u}} (e : X ≅ Spec (.of B)) : Cone (affineDiagram R B) where
  pt := X
  π := ((Functor.const _).map e.hom) ≫ (affineCone R B).π

/-- The cone based at the actual chart is a limit. -/
def chartConeIsLimit {X : Scheme.{u}} (e : X ≅ Spec (.of B)) :
    IsLimit (chartCone R B e) := by
  apply IsLimit.ofIsoLimit (affineIsLimit R B)
  exact Cone.ext e.symm (by intro i; simp [chartCone])

/-- Each projection from the original chart respects its structure morphism. -/
theorem chartCone_over {X : Scheme.{u}} (e : X ≅ Spec (.of B))
    (i : (Finset (relationIdeal R B))ᵒᵖ) :
    (chartCone R B e).π.app i ≫ (affineStructure R B).app i =
      e.hom ≫ Spec.map (CommRingCat.ofHom (algebraMap R B)) := by
  change (e.hom ≫ (affineCone R B).π.app i) ≫ _ = _
  exact (Category.assoc _ _ _).trans
    (congrArg (fun g ↦ e.hom ≫ g) (affineProjection_over R B i.unop))

end

/-- Every finite-type affine chart admits an actual inverse system of finitely presented models. -/
theorem exists_affine_model_system {X : Scheme.{u}} [IsAffine X]
    {R : CommRingCat.{u}} (f : X ⟶ Spec R) [LocallyOfFiniteType f] :
    ∃ (n : ℕ) (I : Ideal (MvPolynomial (Fin n) R))
      (D : (Finset I)ᵒᵖ ⥤ Scheme.{u})
      (π : (Functor.const _).obj X ⟶ D)
      (b : D ⟶ (Functor.const _).obj (Spec R)),
      Nonempty (IsLimit (Cone.mk X π)) ∧
      (∀ i, IsAffine (D.obj i) ∧ LocallyOfFinitePresentation (b.app i) ∧
        QuasiCompact (b.app i)) ∧
      (∀ (i j) (h : i ⟶ j), IsClosedImmersion (D.map h)) ∧
      (∀ i, π.app i ≫ b.app i = f) := by
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (X.isoSpec.inv ≫ f)
  have hfinite : LocallyOfFiniteType (Spec.map φ) := by
    rw [hφ]
    infer_instance
  have hring : φ.hom.FiniteType :=
    (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mp hfinite
  let _ := φ.hom.toAlgebra
  let _ : Algebra.FiniteType R Γ(X, ⊤) := hring
  let D := affineDiagram R Γ(X, ⊤)
  let c := chartCone R Γ(X, ⊤) X.isoSpec
  let b := affineStructure R Γ(X, ⊤)
  refine ⟨numGenerators R Γ(X, ⊤), relationIdeal R Γ(X, ⊤), D, c.π, b,
    ⟨chartConeIsLimit R Γ(X, ⊤) X.isoSpec⟩, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_, ?_⟩
    · change IsAffine (Spec (.of (Stage R Γ(X, ⊤) i.unop)))
      infer_instance
    · exact affineStage_locallyOfFinitePresentation R Γ(X, ⊤) i.unop
    · change QuasiCompact
        (FiniteRelationModel.stageStructure R (relationIdeal R Γ(X, ⊤)) i.unop)
      dsimp [FiniteRelationModel.stageStructure]
      infer_instance
  · intro i j h
    exact FiniteRelationModel.spectrumMap_isClosedImmersion R _ h
  · intro i
    change (chartCone R Γ(X, ⊤) X.isoSpec).π.app i ≫
      (affineStructure R Γ(X, ⊤)).app i = f
    rw [chartCone_over]
    change X.isoSpec.hom ≫ Spec.map φ = f
    rw [hφ, Iso.hom_inv_id_assoc]

end FLT.Mazur.FiniteTypeRelationModel
