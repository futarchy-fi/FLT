/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeFppfFamilyCover
public import FLT.Mazur.SchemeEffectiveEpiSections

/-!
# Detecting full relation equations on an actual fppf cover

The original morphisms and regular functions are determined by their pullbacks
on every member of the cover. Thus the equalizer of the original endpoints is
exactly the intersection of the equalizers on the covering branches.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
universe u
namespace FLT.Mazur.SchemeFppfFamily
open SchemeEffectiveEpiSections
variable {D : Scheme.{u}} (C : Scheme.Cover.{u} Scheme.fppfPrecoverage D)

/-- An actual fppf covering family detects equality of complete scheme morphisms. -/
theorem cover_hom_ext {Y : Scheme.{u}} {a b : D ⟶ Y}
    (h : ∀ i, C.f i ≫ a = C.f i ≫ b) : a = b := by
  apply (cancel_epi (projection C)).mp
  apply Sigma.hom_ext
  intro i
  simpa only [inclusion_projection_assoc] using h i

/-- Pullback to all members of the cover detects equality of original regular functions. -/
theorem cover_sections_ext {s t : Γ(D, ⊤)} (h : ∀ i, (C.f i).appTop s = (C.f i).appTop t) :
    s = t := by
  apply (functionEquiv D).symm.injective
  apply cover_hom_ext C
  intro i
  apply (functionEquiv (C.X i)).injective
  simpa only [functionEquiv_comp, Equiv.apply_symm_apply] using h i

variable {A : Scheme.{u}} (p q : D ⟶ A)

/-- A map coequalizes the full relation exactly when it coequalizes every covering branch. -/
theorem coequalizes_iff {Y : Scheme.{u}} (g : A ⟶ Y) :
    p ≫ g = q ≫ g ↔ ∀ i, C.f i ≫ p ≫ g = C.f i ≫ q ≫ g := by
  constructor
  · intro h i
    rw [h]
  · exact cover_hom_ext C

/-- Branchwise coefficient equations are exactly the original full invariant condition. -/
theorem mem_compatibleFunctions_iff (s : Γ(A, ⊤)) :
    s ∈ compatibleFunctions p q ↔
      ∀ i, s ∈ compatibleFunctions (C.f i ≫ p) (C.f i ≫ q) := by
  change p.appTop s = q.appTop s ↔ ∀ i, (C.f i ≫ p).appTop s = (C.f i ≫ q).appTop s
  simp only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply]
  exact ⟨fun h i ↦ congrArg (fun t ↦ (C.f i).appTop t) h, cover_sections_ext C⟩

/-- The actual invariant subring is the intersection of the branch equalizer subrings. -/
theorem compatibleFunctions_eq_iInf :
    compatibleFunctions p q = ⨅ i, compatibleFunctions (C.f i ≫ p) (C.f i ≫ q) := by
  ext s
  simp only [Subring.mem_iInf]
  exact mem_compatibleFunctions_iff C p q s

end FLT.Mazur.SchemeFppfFamily
