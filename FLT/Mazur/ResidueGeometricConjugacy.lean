/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeometricCoefficientAutomorphisms
public import FLT.Mazur.GeometricResidueMorphismConjugacy
public import Mathlib.AlgebraicGeometry.Morphisms.Preimmersion

/-!
# Conjugacy over the unchanged original coefficient scheme

A residue-field preimmersion allows the algebraic-closure conjugacy theorem
to apply to independent morphisms over the original scheme. The constructed
fiber action also fixes the original projection, without replacing the base.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.ResidueGeometricConjugacy
open GeometricCoefficientAutomorphisms
set_option backward.isDefEq.respectTransparency false
variable {k K : Type} [Field k] [Field K] [Algebra k K]
  {S X Y V : Scheme} (t : Spec (.of k) ⟶ S)
local notation "c" => Spec.map (CommRingCat.ofHom (algebraMap k K))

/-- Coefficient automorphisms fix the entire original geometric base morphism. -/
@[reassoc]
theorem specAction_original (σ : K ≃ₐ[k] K) : (specAction σ).hom ≫ c ≫ t = c ≫ t := by
  rw [← Category.assoc, specAction_base]

/-- The original cartesian fiber carries the complete residue-coefficient action. -/
def fiberAction {a : Y ⟶ V} {b : Y ⟶ Spec (.of K)} {f : V ⟶ S}
    (H : IsPullback a b f (c ≫ t)) : (K ≃ₐ[k] K) →* Aut Y :=
  CartesianFiberAutomorphismAction.action H specAction (specAction_original t)

@[reassoc (attr := simp)]
theorem fiberAction_fst {a : Y ⟶ V} {b : Y ⟶ Spec (.of K)} {f : V ⟶ S}
    (H : IsPullback a b f (c ≫ t)) (σ : K ≃ₐ[k] K) :
    (fiberAction t H σ).hom ≫ a = a :=
  CartesianFiberAutomorphismAction.action_fst H specAction (specAction_original t) σ

@[reassoc (attr := simp)]
theorem fiberAction_snd {a : Y ⟶ V} {b : Y ⟶ Spec (.of K)} {f : V ⟶ S}
    (H : IsPullback a b f (c ≫ t)) (σ : K ≃ₐ[k] K) :
    (fiberAction t H σ).hom ≫ b = b ≫ (specAction σ).hom :=
  CartesianFiberAutomorphismAction.action_snd H specAction (specAction_original t) σ

/-- Independent whole morphisms over the original base are conjugate at the same image point. -/
theorem exists_conjugacy [IsPreimmersion t] [IsAlgClosed K] [Algebra.IsAlgebraic k K]
    (f : X ⟶ S) (p q : Spec (.of K) ⟶ X)
    (hp : p ≫ f = c ≫ t) (hq : q ≫ f = c ≫ t) (hx : p default = q default) :
    ∃ σ : K ≃ₐ[k] K, (specAction σ).inv ≫ p = q := by
  let P := pullback f t
  let p' : Spec (.of K) ⟶ P := pullback.lift p c hp
  let q' : Spec (.of K) ⟶ P := pullback.lift q c hq
  have hpq : p' default = q' default := by
    apply (pullback.fst f t).isEmbedding.injective
    change (p' ≫ pullback.fst f t) default = (q' ≫ pullback.fst f t) default
    simpa only [p', q', pullback.lift_fst] using hx
  obtain ⟨σ, hσ⟩ := GeometricResidueMorphismConjugacy.exists_conjugacy
    (pullback.snd f t) p' q' (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) hpq
  refine ⟨σ, ?_⟩
  have h := congrArg (fun g : Spec (.of K) ⟶ P ↦ g ≫ pullback.fst f t) hσ
  change Spec.map (CommRingCat.ofHom σ.toRingHom) ≫ p = q
  simpa only [Category.assoc, p', q', pullback.lift_fst] using h

end FLT.Mazur.ResidueGeometricConjugacy
