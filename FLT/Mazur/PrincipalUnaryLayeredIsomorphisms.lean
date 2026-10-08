/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalUnaryIncidenceRefinement
public import FLT.Mazur.PrincipalLayeredDirected
public import FLT.Mazur.PrincipalLayeredPathEquations

/-!
# Shared-source isomorphisms in layered incidence systems

For a lower layer with separate outgoing targets, actual isomorphisms can be
imposed without losing the shared middle stages or any refinement square.
Finite equations of two-edge paths are then imposed with this entire lower
isomorphism layer fixed.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z v'

variable {R : Type u} [CommRing R] {ι : Type v} {J : ι → Type w}
  [∀ i, Finite (J i)] {τ : Type z} {F : τ → Type v'} [∀ k, Finite (F k)]
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : (Σ i, J i) → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {C : τ → Type u} [∀ k, CommRing (C k)] [∀ k, Algebra R (C k)]
  [∀ k, Algebra.FiniteType R (C k)]
  {mid : ∀ k, F k → Σ i, J i} {a : ∀ i, A i} {b : ∀ j, B j} {c : ∀ k, C k}
  (e : ∀ j : Σ i, J i, Localization.Away (a j.1) ≃ₐ[R] Localization.Away (b j))
  {g : ∀ k h, Localization.Away (b (mid k h)) →ₐ[R] Localization.Away (c k)}

/-- An actual lower isomorphism refinement extends through the upper incidence layer. -/
theorem exists_principalUnaryLayered_bijective
    (x : PrincipalLayeredStage (fun j (_ : Unit) ↦ j.1) mid a b c
      (fun j _ ↦ (e j).toAlgHom) g) :
    ∃ y : PrincipalLayeredStage (fun j (_ : Unit) ↦ j.1) mid a b c
      (fun j _ ↦ (e j).toAlgHom) g,
      x ≤ y ∧ ∀ j k, Function.Bijective (y.lower.hom j k) := by
  obtain ⟨l, hxl, hl⟩ := exists_principalUnaryIncidence_bijective e x.lower
  obtain ⟨y, hxy, hy, _⟩ := exists_principalLayeredStage_extension_over x l hxl x.target
  refine ⟨y, hxy, ?_⟩
  rw [hy]
  exact hl

variable {ν : τ → Type} [∀ k, Finite (ν k)] (s : ∀ k, ν k → ι)
  (p q : ∀ k n, PrincipalLayeredPath (fun j (_ : Unit) ↦ j.1) mid (s k n) k)

/-- Original path equalities and shared-source lower isomorphisms hold at one common stage. -/
theorem exists_principalUnaryLayered_bijective_pathEquations
    (he : ∀ k n,
      principalLayeredPathMap (a := a) (b := b) (c := c)
          (f := fun j _ ↦ (e j).toAlgHom) (g := g) (p k n) =
        principalLayeredPathMap (a := a) (b := b) (c := c)
          (f := fun j _ ↦ (e j).toAlgHom) (g := g) (q k n))
    (x : PrincipalLayeredStage (fun j (_ : Unit) ↦ j.1) mid a b c
      (fun j _ ↦ (e j).toAlgHom) g) :
    ∃ y : PrincipalLayeredStage (fun j (_ : Unit) ↦ j.1) mid a b c
      (fun j _ ↦ (e j).toAlgHom) g, x ≤ y ∧
      (∀ j k, Function.Bijective (y.lower.hom j k)) ∧ PrincipalLayeredPathEquations s p q y := by
  obtain ⟨z, hxz, hz⟩ := exists_principalUnaryLayered_bijective e x
  obtain ⟨y, hzy, hy, heq⟩ := exists_principalLayeredPathEquations s p q he z
  refine ⟨y, hxz.trans hzy, ?_, heq⟩
  rw [hy]
  exact hz

end FLT.Mazur.FiniteTypeRelationModel
