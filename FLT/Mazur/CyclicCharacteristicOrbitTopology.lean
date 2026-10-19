/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicOrbit
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# The topological quotient of the full normalized comparison relation

An open second projection makes the actual orbit projection open. Continuous
invariant maps descend uniquely using the full comparison scheme.
This construction does not yet establish a scheme structure on the quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
universe v
namespace FLT.Mazur.CyclicCharacteristicOrbit
open CyclicCharacteristicAtlas
variable (n : ℕ) [NeZero n]
local notation "U" => normalizedDisjointSource n
local notation "A" => disjointComparisonArrows n
local notation "src" => disjointComparisonSource n
local notation "tgt" => disjointComparisonTarget n

instance orbitTopology : TopologicalSpace (Orbit n) :=
  inferInstanceAs (TopologicalSpace (Quotient (orbitSetoid n)))

/-- The source projection carries the quotient topology. -/
theorem projection_isQuotientMap : IsQuotientMap (projection n) :=
  isQuotientMap_quotient_mk'

/-- The orbit projection is continuous. -/
theorem projection_continuous : Continuous (projection n) :=
  (projection_isQuotientMap n).continuous

/-- Saturation is computed by the actual scheme relation, not by iterating a closure. -/
theorem saturation_eq (V : Set U) :
    projection n ⁻¹' (projection n '' V) = tgt '' (src ⁻¹' V) := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha, hb⟩ := (projection_eq_iff n y x).mp he
    exact ⟨a, by change src a ∈ V; rw [ha]; exact hy, hb⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨src a, ha, projection_pair n a⟩

/-- An open relation projection makes saturation of every open open. -/
theorem projection_isOpenMap (hq : IsOpenMap tgt) : IsOpenMap (projection n) := by
  intro V hV
  apply (projection_isQuotientMap n).isOpen_preimage.mp
  rw [saturation_eq]
  exact hq _ (hV.preimage (src).continuous)

/-- The orbit projection is an open quotient map when the relation projection is open. -/
theorem projection_isOpenQuotientMap (hq : IsOpenMap tgt) :
    IsOpenQuotientMap (projection n) :=
  .of_isOpenMap_isQuotientMap (projection_isOpenMap n hq) (projection_isQuotientMap n)

/-- The constructed topological orbit space. -/
def space : TopCat := TopCat.of (Orbit n)

/-- The quotient map as a morphism of topological spaces. -/
def quotientMap : (U).toTopCat ⟶ space n :=
  TopCat.ofHom ⟨projection n, projection_continuous n⟩

/-- A function equal on the actual relation descends to the orbit type. -/
def descend {Y : Type v} (g : U → Y) (hg : ∀ a, g (src a) = g (tgt a)) :
    Orbit n → Y :=
  Quotient.lift g fun _ _ ⟨a, ha, hb⟩ ↦ ha ▸ hb ▸ hg a

/-- The descended function recovers the prescribed function on every source point. -/
theorem descend_projection {Y : Type v} (g : U → Y)
    (hg : ∀ a, g (src a) = g (tgt a)) (x : U) :
    descend n g hg (projection n x) = g x := rfl

/-- Descent preserves continuity because the orbit map has the quotient topology. -/
theorem descend_continuous {Y : Type v} [TopologicalSpace Y] (g : U → Y)
    (hg : ∀ a, g (src a) = g (tgt a)) (hc : Continuous g) :
    Continuous (descend n g hg) :=
  (projection_isQuotientMap n).continuous_iff.mpr hc

/-- Descent is unique on the actual point quotient. -/
theorem descend_unique {Y : Type v} (g : U → Y)
    (hg : ∀ a, g (src a) = g (tgt a)) (k : Orbit n → Y)
    (hk : ∀ x, k (projection n x) = g x) : k = descend n g hg := by
  funext z
  obtain ⟨x, rfl⟩ := projection_surjective n z
  exact hk x

end FLT.Mazur.CyclicCharacteristicOrbit
