/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyFunctionDescent

/-!
# Full relation descent on a covering atlas

The coefficient equalizer on the entire source is recovered from chart
functions satisfying all mixed relation tests. Reflexivity supplies the
ordinary overlap equations; the full relation supplies the remaining descent.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeFppfRelationDescent
universe u
variable {X D : Scheme.{u}} (p q : D ⟶ X)
  (C : Scheme.Cover.{u} Scheme.fppfPrecoverage X)

/-- The actual equalizer of the two full relation pullbacks. -/
def invariants : Subring Γ(X, ⊤) := RingHom.eqLocus p.appTop.hom q.appTop.hom

/-- Chart coefficients tested on every pair of independently chosen relation endpoints. -/
def Compatible (v : ∀ a, Γ(C.X a, ⊤)) : Prop :=
  ∀ (T : Scheme.{u}) (a b : C.I₀) (g : T ⟶ C.X a) (h : T ⟶ C.X b)
    (w : T ⟶ D), w ≫ p = g ≫ C.f a → w ≫ q = h ≫ C.f b →
      g.appTop (v a) = h.appTop (v b)

/-- Restriction of an actual invariant coefficient to the whole covering family. -/
def restriction : invariants p q →+* ∀ a, Γ(C.X a, ⊤) :=
  RingHom.pi (fun a ↦ (C.f a).appTop.hom.comp (invariants p q).subtype)

/-- The atlas detects equality in the original full relation equalizer. -/
theorem restriction_injective : Function.Injective (restriction p q C) := by
  intro a b h
  apply Subtype.ext
  exact SchemeFppfFamily.cover_sections_ext C (fun i ↦ congrFun h i)

/-- Restricting an invariant section gives every mixed relation equation. -/
theorem restriction_compatible (v : invariants p q) :
    Compatible p q C (restriction p q C v) := by
  intro T a b g h w hp hq
  change g.appTop ((C.f a).appTop v.val) = h.appTop ((C.f b).appTop v.val)
  simp only [← ConcreteCategory.comp_apply, ← Scheme.Hom.comp_appTop, ← hp, ← hq]
  have hv := v.property
  change p.appTop v.val = q.appTop v.val at hv
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using
    congrArg (fun z ↦ w.appTop z) hv

variable (r : X ⟶ D) (hrp : r ≫ p = 𝟙 X) (hrq : r ≫ q = 𝟙 X)
include r hrp hrq

/-- Full mixed equations construct a unique coefficient on the unchanged source. -/
theorem compatible_existsUnique (v : ∀ a, Γ(C.X a, ⊤))
    (hv : Compatible p q C v) :
    ∃! t : invariants p q, restriction p q C t = v := by
  obtain ⟨t, ht, _⟩ := SchemeFppfFamily.family_sections_existsUnique C v (by
    intro T a b g h hh
    apply hv T a b g h (g ≫ C.f a ≫ r)
    · simp only [Category.assoc, hrp, Category.comp_id]
    · simpa only [Category.assoc, hrq, Category.comp_id] using hh)
  have he : p.appTop t = q.appTop t := by
    apply SchemeFppfFamily.relation_eq_of_chart_tests C p q t
    intro T a b g h w hp hq
    rw [ht a, ht b]
    exact hv T a b g h w hp hq
  refine ⟨⟨t, he⟩, funext ht, fun z hz ↦ ?_⟩
  apply restriction_injective p q C
  exact hz.trans (funext ht).symm

/-- The image of actual restriction is exactly the full mixed-compatible families. -/
theorem mem_range_restriction_iff (v : ∀ a, Γ(C.X a, ⊤)) :
    v ∈ Set.range (restriction p q C) ↔ Compatible p q C v := by
  constructor
  · rintro ⟨t, rfl⟩
    exact restriction_compatible p q C t
  · intro hv
    obtain ⟨t, ht, _⟩ := compatible_existsUnique p q C r hrp hrq v hv
    exact ⟨t, ht⟩

end FLT.Mazur.SchemeFppfRelationDescent
