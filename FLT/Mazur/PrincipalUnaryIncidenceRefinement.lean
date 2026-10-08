/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PrincipalFanIsomorphismRefinement
public import FLT.Mazur.PrincipalBipartiteDirected

/-!
# Isomorphism refinements for shared charts with separate overlap targets

Each chart can have finitely many outgoing occurrences, all using its one
ambient relation set. When each target has one incoming occurrence, the fan
construction gives actual isomorphisms in the existing bipartite incidence
system. Targets shared by different incoming charts require further gluing.
-/

@[expose] public noncomputable section

namespace FLT.Mazur.FiniteTypeRelationModel

universe u v w

variable {R : Type u} [CommRing R] {ι : Type v} {J : ι → Type w}
  {A : ι → Type u} [∀ i, CommRing (A i)] [∀ i, Algebra R (A i)]
  [∀ i, Algebra.FiniteType R (A i)]
  {B : (Σ i, J i) → Type u} [∀ j, CommRing (B j)] [∀ j, Algebra R (B j)]
  [∀ j, Algebra.FiniteType R (B j)]
  {a : ∀ i, A i} {b : ∀ j, B j}
  (e : ∀ j : Σ i, J i, Localization.Away (a j.1) ≃ₐ[R] Localization.Away (b j))

/-- Read every outgoing occurrence of a chart as one shared-source fan. -/
def principalUnaryIncidenceFan
    (x : PrincipalBipartiteStage (fun j (_ : Unit) ↦ j.1) a b
      (fun j _ ↦ (e j).toAlgHom)) (i : ι) :
    PrincipalFanStage (fun _ : J i ↦ a i) (fun j ↦ b ⟨i, j⟩)
      (fun j ↦ (e ⟨i, j⟩).toAlgHom) where
  source := x.source i
  target j := x.target ⟨i, j⟩
  hom j := x.hom ⟨i, j⟩ ()
  fac j := x.fac ⟨i, j⟩ ()

/-- Assemble independent outgoing fans into the existing shared-chart incidence format. -/
def principalUnaryIncidenceOfFans
    (z : ∀ i, PrincipalFanStage (fun _ : J i ↦ a i) (fun j ↦ b ⟨i, j⟩)
      (fun j ↦ (e ⟨i, j⟩).toAlgHom)) :
    PrincipalBipartiteStage (fun j (_ : Unit) ↦ j.1) a b (fun j _ ↦ (e j).toAlgHom) where
  source i := (z i).source
  target j := (z j.1).target j.2
  hom j _ := (z j.1).hom j.2
  fac j _ := (z j.1).fac j.2

/-- Assembly preserves each full coordinate refinement square. -/
theorem principalUnaryIncidenceOfFans_le
    (x : PrincipalBipartiteStage (fun j (_ : Unit) ↦ j.1) a b
      (fun j _ ↦ (e j).toAlgHom))
    (z : ∀ i, PrincipalFanStage (fun _ : J i ↦ a i) (fun j ↦ b ⟨i, j⟩)
      (fun j ↦ (e ⟨i, j⟩).toAlgHom)) (hz : ∀ i, principalUnaryIncidenceFan e x i ≤ z i) :
    x ≤ principalUnaryIncidenceOfFans e z := by
  refine ⟨fun i ↦ (hz i).1, fun j ↦ ?_⟩
  refine ⟨fun _ ↦ (hz j.1).1, principalFan_target_mono (hz j.1) j.2, ?_⟩
  rintro ⟨⟩
  exact principalFan_hom_comm (hz j.1) j.2

variable [∀ i, Finite (J i)]

/-- Each outgoing fan can be refined independently to isomorphisms. -/
theorem exists_principalUnaryIncidenceFan_bijective
    (x : PrincipalBipartiteStage (fun j (_ : Unit) ↦ j.1) a b
      (fun j _ ↦ (e j).toAlgHom)) (i : ι) :
    ∃ y : PrincipalFanStage (fun _ : J i ↦ a i) (fun j ↦ b ⟨i, j⟩)
      (fun j ↦ (e ⟨i, j⟩).toAlgHom),
      principalUnaryIncidenceFan e x i ≤ y ∧ ∀ j, Function.Bijective (y.hom j) := by
  exact exists_principalFan_bijective (R := R) (A := A i) (B := fun j : J i ↦ B ⟨i, j⟩)
    (a := fun _ ↦ a i) (b := fun j ↦ b ⟨i, j⟩)
    (fun j ↦ e ⟨i, j⟩) (principalUnaryIncidenceFan e x i)

/-- A finite number of outgoing overlaps per chart can be made isomorphic simultaneously. -/
theorem exists_principalUnaryIncidence_bijective
    (x : PrincipalBipartiteStage (fun j (_ : Unit) ↦ j.1) a b
      (fun j _ ↦ (e j).toAlgHom)) :
    ∃ y : PrincipalBipartiteStage (fun j (_ : Unit) ↦ j.1) a b
      (fun j _ ↦ (e j).toAlgHom), x ≤ y ∧ ∀ j k, Function.Bijective (y.hom j k) := by
  choose z hxz hz using exists_principalUnaryIncidenceFan_bijective e x
  exact ⟨principalUnaryIncidenceOfFans e z, principalUnaryIncidenceOfFans_le e x z hxz,
    fun j _ ↦ hz j.1 j.2⟩

end FLT.Mazur.FiniteTypeRelationModel
