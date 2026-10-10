/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finite relation ideals from Noetherian coefficient models

Contract the full relation ideal to a Noetherian model, then extend it back.
This produces a finitely generated subideal, functorially for every commuting
map at once. In particular cycles do not require an infinite refinement process.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.NoetherianRelationContraction

universe u v w z

variable {P : Type u} [CommRing P] {P₀ : Type v} [CommRing P₀]
  (c : P₀ →+* P) (I : Ideal P)

/-- Relations visible over a coefficient model, extended to the original ring. -/
def relations : Ideal P := (I.comap c).map c

/-- Every visible relation is an original relation. -/
theorem relations_le : relations c I ≤ I := Ideal.map_comap_le

/-- A Noetherian coefficient model gives finitely many relations over any base. -/
theorem relations_fg [IsNoetherianRing P₀] : (relations c I).FG :=
  (I.comap c).fg_of_isNoetherianRing.map c

/-- Any original relation represented over the coefficient model is retained. -/
theorem mem_relations {x : P₀} (hx : c x ∈ I) : c x ∈ relations c I :=
  Ideal.mem_map_of_mem c hx

/-- All prescribed relations in the coefficient image survive simultaneously. -/
theorem span_le_relations (s : Set P) (hs : s ⊆ I) (hc : s ⊆ Set.range c) :
    Ideal.span s ≤ relations c I := by
  apply Ideal.span_le.mpr
  intro x hx
  obtain ⟨y, rfl⟩ := hc hx
  exact mem_relations c I (hs hx)

variable {Q : Type w} [CommRing Q] {Q₀ : Type z} [CommRing Q₀]

/-- A commuting coefficient square transports the constructed finite relations. -/
theorem map_relations_le (d : Q₀ →+* Q) (J : Ideal Q)
    (f : P →+* Q) (f₀ : P₀ →+* Q₀) (h : f.comp c = d.comp f₀)
    (hf : I ≤ J.comap f) :
    (relations c I).map f ≤ relations d J := by
  change ((I.comap c).map c).map f ≤ (J.comap d).map d
  rw [Ideal.map_map, h, ← Ideal.map_map]
  apply Ideal.map_mono
  apply Ideal.map_le_iff_le_comap.mpr
  intro x hx
  change d (f₀ x) ∈ J
  rw [← RingHom.comp_apply, ← h, RingHom.comp_apply]
  exact hf hx

end FLT.Mazur.NoetherianRelationContraction
