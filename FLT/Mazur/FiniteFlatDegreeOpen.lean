/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ConstantDegree

/-!
# Open degree strata of finite flat finitely presented families

The actual rank function defines clopen constant-degree pieces covering the
base. Each piece represents constant degree after arbitrary base change,
including tests over disconnected bases and the empty degree-zero family.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

set_option backward.isDefEq.respectTransparency false

variable {D S : Scheme.{u}} (f : D ⟶ S)
  [IsFinite f] [Flat f] [LocallyOfFinitePresentation f]

/-- The clopen locus on which the actual finite flat family has degree d. -/
def finiteFlatDegreeOpen (d : ℕ) : S.Opens :=
  ⟨{s | f.finrank s = d}, f.isLocallyConstant_finrank.isOpen_fiber d⟩

@[simp]
lemma mem_finiteFlatDegreeOpen (d : ℕ) (s : S) :
    s ∈ finiteFlatDegreeOpen f d ↔ f.finrank s = d := Iff.rfl

/-- Each degree stratum is also closed in the original base. -/
theorem finiteFlatDegreeOpen_isClosed (d : ℕ) :
    IsClosed (finiteFlatDegreeOpen f d : Set S) :=
  f.isLocallyConstant_finrank.isClosed_fiber d

/-- Every base point belongs to the stratum of its actual fiber rank. -/
theorem iSup_finiteFlatDegreeOpen : ⨆ d, finiteFlatDegreeOpen f d = ⊤ := by
  apply top_unique
  intro s _
  exact Opens.mem_iSup.mpr ⟨f.finrank s, rfl⟩

/-- Distinct degrees give disjoint strata. -/
theorem finiteFlatDegreeOpen_disjoint {d e : ℕ} (h : d ≠ e) :
    Disjoint (finiteFlatDegreeOpen f d) (finiteFlatDegreeOpen f e) := by
  apply disjoint_iff.mpr
  apply bot_unique
  intro s hs
  exact (h (hs.1.symm.trans hs.2)).elim

/-- The full family restricted to its degree stratum has that constant degree. -/
theorem finiteFlatDegreeOpen_degree (d : ℕ) :
    FiniteLocallyFreeDegree (pullback.snd f (finiteFlatDegreeOpen f d).ι) d := by
  refine ⟨inferInstance, inferInstance, inferInstance, fun s ↦ ?_⟩
  rw [Scheme.Hom.finrank_pullback_snd]
  exact s.property

/-- Degree strata commute with every cartesian base change. -/
theorem finiteFlatDegreeOpen_baseChange {P T : Scheme.{u}}
    {a : P ⟶ D} {p : P ⟶ T} {g : T ⟶ S} (h : IsPullback a p f g)
    [IsFinite p] [Flat p] [LocallyOfFinitePresentation p] (d : ℕ) :
    finiteFlatDegreeOpen p d = g ⁻¹ᵁ finiteFlatDegreeOpen f d := by
  ext t
  exact congrArg (· = d) (Scheme.Hom.finrank_of_isPullback a p f g h t) |>.to_iff

/-- The exact constant-degree condition is uniquely represented by the degree open. -/
theorem finiteFlatDegreeOpen_represents {T : Scheme.{u}} (g : T ⟶ S) (d : ℕ) :
    FiniteLocallyFreeDegree (pullback.snd f g) d ↔
      ∃! k : T ⟶ (finiteFlatDegreeOpen f d).toScheme,
        k ≫ (finiteFlatDegreeOpen f d).ι = g := by
  constructor
  · intro hg
    have hr : Set.range g ⊆ Set.range (finiteFlatDegreeOpen f d).ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨t, rfl⟩
      change f.finrank (g t) = d
      rw [← Scheme.Hom.finrank_pullback_snd f g]
      exact hg.2.2.2 t
    refine ⟨IsOpenImmersion.lift _ g hr, IsOpenImmersion.lift_fac _ _ _, ?_⟩
    intro k hk
    rw [← cancel_mono (finiteFlatDegreeOpen f d).ι, hk, IsOpenImmersion.lift_fac]
  · rintro ⟨k, hk, _⟩
    refine ⟨inferInstance, inferInstance, inferInstance, fun t ↦ ?_⟩
    rw [Scheme.Hom.finrank_pullback_snd, ← hk]
    exact (k t).property

end FLT.Mazur.FCurve
