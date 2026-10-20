/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfRelationDescent

/-!
# Exact boundary corrections on a full covering atlas

The boundary kernel is taken on the actual chart pullback. Correcting a
prescribed family in these kernels is equivalent to lifting the boundary
section through the full source equalizer, including every mixed equation.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFppfRelationDescent
variable {X D Z : Scheme.{0}} (p q : D ⟶ X)
  (C : Scheme.Cover.{0} Scheme.fppfPrecoverage X) (i : Z ⟶ X)

/-- Exact boundary values on the original chart pullbacks. -/
def HasBoundary (v : ∀ a, Γ(C.X a, ⊤)) (t : Γ(Z, ⊤)) : Prop :=
  ∀ a, (pullback.snd i (C.f a)).appTop (v a) =
    (pullback.fst i (C.f a)).appTop t

/-- Exact chart boundary equations retain all boundary-valued scheme tests. -/
theorem hasBoundary_test (v : ∀ a, Γ(C.X a, ⊤)) (t : Γ(Z, ⊤))
    (hb : HasBoundary C i v t) {T : Scheme.{0}} (a : C.I₀)
    (u : T ⟶ C.X a) (w : T ⟶ Z) (hu : u ≫ C.f a = w ≫ i) :
    u.appTop (v a) = w.appTop t := by
  have h := congrArg (fun x ↦ (pullback.lift w u hu.symm).appTop x) (hb a)
  simpa only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop,
    pullback.lift_snd, pullback.lift_fst] using h

/-- Chart boundary tests detect the boundary of a descended coefficient. -/
theorem boundary_of_restriction (v : invariants p q) (t : Γ(Z, ⊤))
    (h : HasBoundary C i (restriction p q C v) t) : i.appTop v.val = t := by
  apply SchemeFppfFamily.cover_sections_ext (C.pullback₁ i)
  intro a
  have he := h a
  change (pullback.snd i (C.f a)).appTop ((C.f a).appTop v.val) = _ at he
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop] at he ⊢
  exact (congrArg (fun z ↦ z.appTop v.val)
    (pullback.condition (f := i) (g := C.f a))).trans he

/-- Restriction preserves the exact boundary, without reducing the boundary scheme. -/
theorem restriction_hasBoundary (v : invariants p q) :
    HasBoundary C i (restriction p q C v) (i.appTop v.val) := by
  intro a
  change (pullback.snd i (C.f a)).appTop ((C.f a).appTop v.val) = _
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, pullback.condition]

variable (r : X ⟶ D) (hrp : r ≫ p = 𝟙 X) (hrq : r ≫ q = 𝟙 X)
include r hrp hrq

/-- Full compatible boundary coefficients construct an actual original invariant lift. -/
theorem boundary_lift_of_compatible (v : ∀ a, Γ(C.X a, ⊤)) (t : Γ(Z, ⊤))
    (hv : Compatible p q C v) (hb : HasBoundary C i v t) :
    ∃ u : invariants p q, i.appTop u.val = t ∧ restriction p q C u = v := by
  obtain ⟨u, hu, _⟩ := compatible_existsUnique p q C r hrp hrq v hv
  refine ⟨u, boundary_of_restriction p q C i u t ?_, hu⟩
  rwa [hu]

/-- The exact correction problem on the whole atlas is equivalent to an original lift. -/
theorem lift_iff_boundary_corrections (v : ∀ a, Γ(C.X a, ⊤)) (t : Γ(Z, ⊤))
    (hb : HasBoundary C i v t) :
    (∃ u : invariants p q, i.appTop u.val = t) ↔
      ∃ z : ∀ a, Γ(C.X a, ⊤),
        (∀ a, (pullback.snd i (C.f a)).appTop (z a) = 0) ∧
        Compatible p q C (v - z) := by
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨v - restriction p q C u, ?_, ?_⟩
    · intro a
      change (pullback.snd i (C.f a)).appTop (v a - restriction p q C u a) = 0
      rw [map_sub, hb a, restriction_hasBoundary p q C i u a, hu, sub_self]
    · simpa only [sub_sub_cancel] using restriction_compatible p q C u
  · rintro ⟨z, hz, hc⟩
    obtain ⟨u, hu, _⟩ := boundary_lift_of_compatible p q C i r hrp hrq (v - z) t hc (by
      intro a
      change (pullback.snd i (C.f a)).appTop (v a - z a) = _
      rw [map_sub, hz a, sub_zero]
      exact hb a)
    exact ⟨u, hu⟩

end FLT.Mazur.SchemeFppfRelationDescent
