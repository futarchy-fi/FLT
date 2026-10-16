/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationJointChartCoefficients

/-!
# Exact boundary differences of independently chosen finite-chart lifts

Every pair of actual chart lifts of the same original open section agrees on
the full pulled-back boundary of the common overlap. Their ambient difference
therefore belongs to the actual boundary kernel ideal. Vanishing of this ideal
class is not asserted to give equality of the ambient lifts.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
open InvariantBoundary
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A B C : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p]
  (e : CategoryTheory.EquivalenceRelation p q)
  {I J H : Type} [Fintype I] [Fintype J] [Fintype H] (o : I) (o' : J)
  (α : I ↪ H) (β : J ↪ H)
  (U : (source p q I o).Opens) (V : (source p q J o').Opens)
  (i : B ⟶ A) (z : C ⟶ D) (r s : C ⟶ B)
  (hr : IsPullback z r p i) (hs : z ≫ q = s ≫ i)
local notation "j" => InvariantBoundary.inclusion (p := p) (q := q) H (α o) i
local notation "j₁" => InvariantBoundary.inclusion (p := p) (q := q) I o i
local notation "j₂" => InvariantBoundary.inclusion (p := p) (q := q) J o' i
local notation "b₁" => endpoint (p := p) (q := q) I o i
local notation "b₂" => endpoint (p := p) (q := q) J o' i
local notation "W" => jointChartOpen e o o' α β U V
local notation "F" => jointChartFirst e o o' α β U V
local notation "G" => jointChartSecond e o o' α β U V
local notation "F₀" => jointChartBoundaryFirst e o o' α β U V i z r s hr hs
local notation "G₀" => jointChartBoundarySecond e o o' α β U V i z r s hr hs

include hr hs

/-- Any two actual lifts agree on the entire common boundary, including its nilpotents. -/
theorem jointChart_lifts_boundary_eq (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
    (hU : (j₁) ⁻¹ᵁ U ≤ (b₁) ⁻¹ᵁ E) (hV : (j₂) ⁻¹ᵁ V ≤ (b₂) ⁻¹ᵁ E)
    (t : Γ(E.toScheme, ⊤)) (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)
    (a : Γ(U.toScheme, ⊤)) (b : Γ(V.toScheme, ⊤))
    (ha : ((j₁) ∣_ U).appTop a = ((b₁).resLE E _ hU).appTop t)
    (hb : ((j₂) ∣_ V).appTop b = ((b₂).resLE E _ hV).appTop t) :
    ((j) ∣_ W).appTop ((F).appTop a) = ((j) ∣_ W).appTop ((G).appTop b) := by
  have hf : ((j) ∣_ W).appTop ((F).appTop a) =
      (F₀).appTop (((j₁) ∣_ U).appTop a) := by
    change (((F).appTop ≫ ((j) ∣_ W).appTop) a) =
      ((((j₁) ∣_ U).appTop ≫ (F₀).appTop) a)
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
      jointChartBoundaryFirst_inclusion]
  have hg : ((j) ∣_ W).appTop ((G).appTop b) =
      (G₀).appTop (((j₂) ∣_ V).appTop b) := by
    change (((G).appTop ≫ ((j) ∣_ W).appTop) b) =
      ((((j₂) ∣_ V).appTop ≫ (G₀).appTop) b)
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
      jointChartBoundarySecond_inclusion]
  rw [hf, hg, ha, hb]
  exact jointChart_coefficient e o o' α β U V i z r s hr hs E hE hU hV t ht

/-- The actual ambient discrepancy lies in the exact closed-boundary ideal on the overlap. -/
theorem jointChart_lifts_sub_mem_kernel (E : B.Opens) (hE : r ⁻¹ᵁ E = s ⁻¹ᵁ E)
    (hU : (j₁) ⁻¹ᵁ U ≤ (b₁) ⁻¹ᵁ E) (hV : (j₂) ⁻¹ᵁ V ≤ (b₂) ⁻¹ᵁ E)
    (t : Γ(E.toScheme, ⊤)) (ht : (r ∣_ E).appTop t = (s.resLE E _ hE.le).appTop t)
    (a : Γ(U.toScheme, ⊤)) (b : Γ(V.toScheme, ⊤))
    (ha : ((j₁) ∣_ U).appTop a = ((b₁).resLE E _ hU).appTop t)
    (hb : ((j₂) ∣_ V).appTop b = ((b₂).resLE E _ hV).appTop t) :
    (F).appTop a - (G).appTop b ∈ RingHom.ker ((j) ∣_ W).appTop.hom := by
  change ((j) ∣_ W).appTop ((F).appTop a - (G).appTop b) = 0
  rw [map_sub, sub_eq_zero]
  exact jointChart_lifts_boundary_eq e o o' α β U V i z r s hr hs E hE hU hV t ht a b ha hb

end FLT.Mazur.EquivalenceRelationNormalizedFrames.MixedFrames
