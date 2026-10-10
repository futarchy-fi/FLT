/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalOccurrenceTargetPatchSelection
public import Mathlib.AlgebraicGeometry.Gluing

/-!
# Gluing constrained families of occurrence patches

Any prescribed covering subfamily gives a genuine open cover and a gluing
operation. This does not enlarge the family by diagonal patches.
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

variable {j : κ} {μ : Type*} (c : μ → PrincipalOccurrencePatch (dst := dst) j)
  (hc : (⨆ m, (principalOccurrencePatchOpen x hx (c m)).opensRange) = ⊤)

/-- An actual open cover from precisely the prescribed patch subfamily. -/
def principalOccurrencePatchSubfamilyCover :
    (Spec (.of (PrincipalStage R (B j) (b j) (x.target j)))).OpenCover where
  I₀ := μ
  X m := principalOccurrencePatchScheme x (c m)
  f m := principalOccurrencePatchOpen x hx (c m)
  mem₀ := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨?_, inferInstance⟩
    intro z
    have hz : z ∈ ⨆ m, (principalOccurrencePatchOpen x hx (c m)).opensRange := by
      rw [hc]
      trivial
    obtain ⟨m, hm⟩ := TopologicalSpace.Opens.mem_iSup.mp hz
    exact ⟨m, hm⟩

variable {T : Scheme.{u}} (g : ∀ m, principalOccurrencePatchScheme x (c m) ⟶ T)
  (hg : ∀ m n, principalOccurrenceCrossLeft x hx (c m) (c n) ≫ g m =
    principalOccurrenceCrossRight x hx (c m) (c n) ≫ g n)

/-- Glue on the supplied cover, including covers constrained by a target chart. -/
def principalOccurrencePatchSubfamilyGlue :
    Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) ⟶ T :=
  (principalOccurrencePatchSubfamilyCover x hx c hc).glueMorphisms g hg

/-- The glued morphism recovers every supplied patch map. -/
@[reassoc (attr := simp)] theorem principalOccurrencePatchSubfamilyGlue_fac (m : μ) :
    principalOccurrencePatchOpen x hx (c m) ≫
        principalOccurrencePatchSubfamilyGlue x hx c hc g hg = g m :=
  (principalOccurrencePatchSubfamilyCover x hx c hc).ι_glueMorphisms g hg m

include hc in
/-- The supplied covering patches determine a morphism on the entire overlap. -/
theorem principalOccurrencePatchSubfamily_hom_ext
    (g h : Spec (.of (PrincipalStage R (B j) (b j) (x.target j))) ⟶ T)
    (he : ∀ m, principalOccurrencePatchOpen x hx (c m) ≫ g =
      principalOccurrencePatchOpen x hx (c m) ≫ h) : g = h :=
  (principalOccurrencePatchSubfamilyCover x hx c hc).hom_ext g h he

end FLT.Mazur.FiniteTypeRelationModel
