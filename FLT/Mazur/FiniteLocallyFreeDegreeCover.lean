/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantDegree
public import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation

/-!
# Finite locally free degree from cartesian charts

An actual cartesian family on an open cover determines finiteness, flatness,
finite presentation and the scheme-theoretic rank of the global morphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false

/-- Finite locally free degree can be checked on any explicit cartesian open cover. -/
theorem finiteLocallyFreeDegree_of_cartesianCover {D S : Scheme.{u}} (f : D ⟶ S)
    (C : S.OpenCover) (X : C.I₀ → Scheme.{u})
    (a : ∀ i, X i ⟶ D) (b : ∀ i, X i ⟶ C.X i)
    (h : ∀ i, IsPullback (a i) (b i) f (C.f i)) (d : ℕ)
    (hb : ∀ i, FiniteLocallyFreeDegree (b i) d) : FiniteLocallyFreeDegree f d := by
  have hi : IsFinite f := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @IsFinite) C
    intro i
    change IsFinite (pullback.snd f (C.f i))
    rw [← (h i).isoPullback_inv_snd]
    let _ := (hb i).1
    infer_instance
  have hf : Flat f := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @Flat) C
    intro i
    change Flat (pullback.snd f (C.f i))
    rw [← (h i).isoPullback_inv_snd]
    let _ := (hb i).2.1
    infer_instance
  have hp : LocallyOfFinitePresentation f := by
    apply IsZariskiLocalAtTarget.of_openCover (P := @LocallyOfFinitePresentation) C
    intro i
    change LocallyOfFinitePresentation (pullback.snd f (C.f i))
    rw [← (h i).isoPullback_inv_snd]
    let _ := (hb i).2.2.1
    infer_instance
  refine ⟨hi, hf, hp, fun s ↦ ?_⟩
  obtain ⟨i, x, rfl⟩ := Scheme.Cover.exists_eq C s
  rw [← Scheme.Hom.finrank_of_isPullback (a i) (b i) f (C.f i) (h i) x]
  exact (hb i).2.2.2 x

/-- An actual algebra basis gives finite locally free degree, also over the zero ring. -/
theorem finiteLocallyFreeDegree_spec_of_basis (R A : Type u)
    [CommRing R] [CommRing A] [Algebra R A] (d : ℕ) (b : Module.Basis (Fin d) R A) :
    FiniteLocallyFreeDegree (Spec.map (CommRingCat.ofHom (algebraMap R A))) d := by
  let _ := Module.Free.of_basis b
  let _ := Module.Finite.of_basis b
  let _ := Module.finitePresentation_of_projective R A
  apply (finiteLocallyFreeDegree_spec_algebraMap_iff R A).mpr
  intro p
  let _ := p.nontrivial
  rw [Module.rankAtStalk_eq_finrank_of_free, Module.finrank_eq_card_basis b, Fintype.card_fin]
  rfl

end FLT.Mazur.FCurve
