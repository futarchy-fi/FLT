/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineOpenDenominators
public import FLT.Mazur.ModuleSectionRatioBasicOpen

/-!
# Coordinates on affine section covers

Ratios of actual sections make every pair and triple overlap principal.
Functions on one chart have simultaneous numerators on a finite affine cover.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
universe u v
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.FCurve.SectionCover
variable {X : Scheme.{u}} {L : X.Modules} {ι : Type v}

/-- Restriction of regular functions, as a ring homomorphism. -/
abbrev res {U V : X.Opens} (h : U ≤ V) : Γ(X, V) →+* Γ(X, U) :=
  (X.presheaf.map (homOfLE h).op).hom

/-- Iterated restriction is direct restriction. -/
lemma res_res {U V W : X.Opens} (h : U ≤ V) (k : V ≤ W) (a : Γ(X, W)) :
    res h (res k a) = res (h.trans k) a := by
  simp only [res, ← Functor.map_comp_apply, ← op_comp, homOfLE_comp]

/-- The generator chart of a member of the section family. -/
abbrev chart (s : ι → Γ(L, ⊤)) (i : ι) := sectionGeneratorOpen L (s i)

/-- Coordinates relative to a generator on any subopen of its chart. -/
abbrev ratio (s : ι → Γ(L, ⊤)) (j i : ι) (U : X.Opens) (h : U ≤ chart s j) :=
  sectionRatioOn L (s j) U h (s i)

/-- Coordinates restrict to the same ratios on smaller opens. -/
lemma res_ratio (s : ι → Γ(L, ⊤)) (j i : ι) {U V : X.Opens}
    (h : U ≤ V) (hV : V ≤ chart s j) :
    res h (ratio s j i V hV) = ratio s j i U (h.trans hV) :=
  sectionRatioOn_restrict L (s j) V U hV h (s i)

/-- Coordinate multiplication on a common generator chart. -/
lemma ratio_mul (s : ι → Γ(L, ⊤)) (j k i : ι) (U : X.Opens)
    (hj : U ≤ chart s j) (hk : U ≤ chart s k) :
    ratio s j k U hj * ratio s k i U hk = ratio s j i U hj :=
  sectionRatioOn_change L (s j) (s k) (s i) U hj hk

/-- A section overlap is the principal open of its ratio. -/
lemma inf_eq_basicOpen (s : ι → Γ(L, ⊤)) (j i : ι) (U : X.Opens)
    (h : U ≤ chart s j) :
    U ⊓ chart s i = X.basicOpen (ratio s j i U h) :=
  (sectionRatioOn_basicOpen L (s j) (s i) U h).symm

/-- Pair overlaps of affine section charts are affine over arbitrary rings. -/
lemma isAffineOpen_inf (s : ι → Γ(L, ⊤)) (h : ∀ i, IsAffineOpen (chart s i))
    (j k : ι) : IsAffineOpen (chart s j ⊓ chart s k) := by
  rw [inf_eq_basicOpen s j k _ le_rfl]
  exact (h j).basicOpen _

/-- One exponent clears the restrictions of a function on a chosen chart. -/
theorem chart_numerators [Finite ι] (s : ι → Γ(L, ⊤))
    (h : ∀ j, IsAffineOpen (chart s j)) (i : ι) (a : Γ(X, chart s i)) :
    ∃ (N : ℕ) (b : ∀ j, Γ(X, chart s j)), ∀ j,
      res inf_le_left (b j) = ratio s j i (chart s j ⊓ chart s i) inf_le_left ^ N *
        res inf_le_right a := by
  obtain ⟨N, b, hb⟩ := AffineOpenDenominators.finite_numerators
    (chart s) (fun j ↦ chart s j ⊓ chart s i) h
    (fun j ↦ ratio s j i (chart s j) le_rfl)
    (fun j ↦ inf_eq_basicOpen s j i _ le_rfl) (fun _ ↦ res inf_le_right a)
  refine ⟨N, b, fun j ↦ ?_⟩
  simpa only [← res_ratio s j i inf_le_left le_rfl] using hb j

/-- The difference of two chart coefficients, in the first generator's coordinates. -/
def discrepancy (s : ι → Γ(L, ⊤)) (N : ℕ) (b : ∀ j, Γ(X, chart s j)) (j k : ι) :
    Γ(X, chart s j ⊓ chart s k) :=
  res inf_le_left (b j) - ratio s j k _ inf_le_left ^ N * res inf_le_right (b k)

end FLT.Mazur.FCurve.SectionCover
