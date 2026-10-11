/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeRelationOrbit
public import Mathlib.Topology.Maps.OpenQuotient

/-!
# The open topological quotient of a relative scheme relation

An open second projection makes the actual orbit projection open. Continuous
invariant maps descend uniquely; in particular the map to the original base
descends. These constructions do not claim a scheme structure on the quotient.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Topology
universe u v
namespace FLT.Mazur.RelativeRelationOrbit
variable {S : Scheme.{u}} {A U : Over S} {p q : A ⟶ U}
  (e : CategoryTheory.EquivalenceRelation p q)

instance orbitTopology : TopologicalSpace (Orbit e) :=
  inferInstanceAs (TopologicalSpace (Quotient (orbitSetoid e)))

/-- The source projection carries the quotient topology. -/
theorem projection_isQuotientMap : IsQuotientMap (projection e) :=
  isQuotientMap_quotient_mk'

/-- The orbit projection is continuous. -/
theorem projection_continuous : Continuous (projection e) :=
  (projection_isQuotientMap e).continuous

/-- Saturation is computed by the actual scheme relation, not by iterating a closure. -/
theorem saturation_eq (V : Set U.left) :
    projection e ⁻¹' (projection e '' V) = q.left '' (p.left ⁻¹' V) := by
  ext x
  constructor
  · rintro ⟨y, hy, he⟩
    obtain ⟨a, ha, hb⟩ := (projection_eq_iff e y x).mp he
    exact ⟨a, by change p.left a ∈ V; rw [ha]; exact hy, hb⟩
  · rintro ⟨a, ha, rfl⟩
    exact ⟨p.left a, ha, projection_pair e a⟩

/-- An open relation projection makes saturation of every open open. -/
theorem projection_isOpenMap (hq : IsOpenMap q.left) : IsOpenMap (projection e) := by
  intro V hV
  apply (projection_isQuotientMap e).isOpen_preimage.mp
  rw [saturation_eq]
  exact hq _ (hV.preimage p.left.continuous)

/-- The orbit projection is an open quotient map when the relation projection is open. -/
theorem projection_isOpenQuotientMap (hq : IsOpenMap q.left) :
    IsOpenQuotientMap (projection e) :=
  .of_isOpenMap_isQuotientMap (projection_isOpenMap e hq) (projection_isQuotientMap e)

/-- The constructed topological orbit space. -/
def space : TopCat.{u} := TopCat.of (Orbit e)

/-- The quotient map as a morphism of topological spaces. -/
def quotientMap : U.left.toTopCat ⟶ space e :=
  TopCat.ofHom ⟨projection e, projection_continuous e⟩

/-- A function equal on the actual relation descends to the orbit type. -/
def descend {Y : Type v} (g : U.left → Y) (hg : ∀ a, g (p.left a) = g (q.left a)) :
    Orbit e → Y :=
  Quotient.lift g fun _ _ ⟨a, ha, hb⟩ ↦ ha ▸ hb ▸ hg a

/-- The descended function recovers the prescribed function on every source point. -/
theorem descend_projection {Y : Type v} (g : U.left → Y)
    (hg : ∀ a, g (p.left a) = g (q.left a)) (x : U.left) :
    descend e g hg (projection e x) = g x := rfl

/-- Descent preserves continuity because the orbit map has the quotient topology. -/
theorem descend_continuous {Y : Type v} [TopologicalSpace Y] (g : U.left → Y)
    (hg : ∀ a, g (p.left a) = g (q.left a)) (hc : Continuous g) :
    Continuous (descend e g hg) :=
  (projection_isQuotientMap e).continuous_iff.mpr hc

/-- Descent is unique on the actual point quotient. -/
theorem descend_unique {Y : Type v} (g : U.left → Y)
    (hg : ∀ a, g (p.left a) = g (q.left a)) (k : Orbit e → Y)
    (hk : ∀ x, k (projection e x) = g x) : k = descend e g hg := by
  funext z
  obtain ⟨x, rfl⟩ := projection_surjective e z
  exact hk x

/-- The two relation projections have exactly the same original base point. -/
theorem base_invariant (a : A.left) : U.hom (p.left a) = U.hom (q.left a) := by
  exact (congrArg (fun k ↦ k a) (Over.w p)).trans
    (congrArg (fun k ↦ k a) (Over.w q)).symm

/-- The orbit space retains its original map to the base as a continuous map. -/
def baseMap : space e ⟶ S.toTopCat :=
  TopCat.ofHom ⟨descend e U.hom (base_invariant (p := p) (q := q)),
    descend_continuous e U.hom (base_invariant (p := p) (q := q)) U.hom.continuous⟩

/-- The descended structural map factors the original one. -/
theorem quotientMap_baseMap : quotientMap e ≫ baseMap e = U.hom.base := rfl

end FLT.Mazur.RelativeRelationOrbit
