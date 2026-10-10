/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceCrossChartIntersections
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing the occurrence patches of a shared overlap

All incoming ambient charts contribute double-open patches. A diagonal
patch already covers the shared overlap, so the entire family is a genuine
open cover. Cross-chart pullbacks give the compatibility test for gluing.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w z

variable {R : Type u} [CommRing R] {ι : Type v} {κ : Type w} {J : ι → Type z}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : κ → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {dst : ∀ i, J i → κ} {a : ∀ i, J i → A i} {b : ∀ j, B j}
  {f : ∀ i e, Localization.Away (a i e) →ₐ[R] Localization.Away (b (dst i e))}
  (x : PrincipalOccurrenceStage dst a b f) (hx : ∀ i e, Function.Bijective (x.hom i e))

/-- The diagonal double open is the whole shared overlap. -/
instance principalOccurrenceDiagonalPatch_isIso (i : ι) (e : J i) :
    IsIso (principalOccurrencePatchOpen x hx ⟨⟨⟨i, e⟩, rfl⟩, e⟩) := by
  rw [← (principalOccurrencePatch_isPullback x hx i e e).isoPullback_hom_fst]
  infer_instance

/-- Every overlap with an incoming occurrence is covered by its cross-chart patches. -/
def principalOccurrencePatchCover {j : κ} (e : PrincipalIncoming (dst := dst) j) :
    (Spec (.of (PrincipalStage R (B j) (b j) (x.target j)))).OpenCover where
  I₀ := PrincipalOccurrencePatch (dst := dst) j
  X p := principalOccurrencePatchScheme x p
  f p := principalOccurrencePatchOpen x hx p
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro y
    obtain ⟨⟨i, k⟩, rfl⟩ := e
    exact ⟨⟨⟨⟨i, k⟩, rfl⟩, k⟩,
      (principalOccurrencePatchOpen x hx ⟨⟨⟨i, k⟩, rfl⟩, k⟩).homeomorph.surjective y⟩

/-- Glue compatible local maps using intersections across all incoming ambient charts. -/
def principalOccurrencePatchGlue {j : κ} (e : PrincipalIncoming (dst := dst) j)
    {T : Scheme.{u}} (g : ∀ p : PrincipalOccurrencePatch (dst := dst) j,
      principalOccurrencePatchScheme x p ⟶ T)
    (hg : ∀ p q, principalOccurrenceCrossLeft x hx p q ≫ g p =
      principalOccurrenceCrossRight x hx p q ≫ g q) :
    Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) ⟶ T :=
  (principalOccurrencePatchCover x hx e).glueMorphisms g hg

/-- The glued map recovers every patch, including those from different charts. -/
@[reassoc (attr := simp)] theorem principalOccurrencePatchGlue_fac {j : κ}
    (e : PrincipalIncoming (dst := dst) j) {T : Scheme.{u}}
    (g : ∀ p : PrincipalOccurrencePatch (dst := dst) j,
      principalOccurrencePatchScheme x p ⟶ T)
    (hg : ∀ p q, principalOccurrenceCrossLeft x hx p q ≫ g p =
      principalOccurrenceCrossRight x hx p q ≫ g q)
    (p : PrincipalOccurrencePatch (dst := dst) j) :
    principalOccurrencePatchOpen x hx p ≫ principalOccurrencePatchGlue x hx e g hg = g p :=
  (principalOccurrencePatchCover x hx e).ι_glueMorphisms g hg p

/-- Equality of global shared-overlap maps can be checked on all cross-chart patches. -/
theorem principalOccurrencePatch_hom_ext {j : κ} (e : PrincipalIncoming (dst := dst) j)
    {T : Scheme.{u}} (g h : Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) ⟶ T)
    (he : ∀ p : PrincipalOccurrencePatch (dst := dst) j,
      principalOccurrencePatchOpen x hx p ≫ g = principalOccurrencePatchOpen x hx p ≫ h) :
    g = h :=
  (principalOccurrencePatchCover x hx e).hom_ext g h he

/-- The overlap gluing does not depend on the incoming occurrence used to prove coverage. -/
theorem principalOccurrencePatchGlue_independent {j : κ}
    (e d : PrincipalIncoming (dst := dst) j) {T : Scheme.{u}}
    (g : ∀ p : PrincipalOccurrencePatch (dst := dst) j,
      principalOccurrencePatchScheme x p ⟶ T)
    (hg : ∀ p q, principalOccurrenceCrossLeft x hx p q ≫ g p =
      principalOccurrenceCrossRight x hx p q ≫ g q) :
    principalOccurrencePatchGlue x hx e g hg = principalOccurrencePatchGlue x hx d g hg := by
  apply principalOccurrencePatch_hom_ext x hx e
  intro p
  rw [principalOccurrencePatchGlue_fac, principalOccurrencePatchGlue_fac]

end FLT.Mazur.FiniteTypeRelationModel
