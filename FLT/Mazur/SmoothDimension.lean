/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FCurveContracts

/-!
# Reduction of smooth curve dimension to standard-smooth algebras

Topological dimension is local on a scheme, with no quasi-compactness hypothesis.
We extract nonempty standard-smooth affine charts over the original field and
reduce `SmoothCurveDimension` to the Krull dimension of their coordinate rings.
The algebraic dimension theorem remains an explicit hypothesis of the reduction.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace FLT.Mazur.FCurve

section Topology

variable {T : Type u} [TopologicalSpace T] [QuasiSober T] [T0Space T]

attribute [local instance] specializationOrder

/-- Dimension is the supremum of point coheights in a sober space. -/
theorem topologicalKrullDim_eq_iSup_coheight :
    topologicalKrullDim T = ⨆ x : T, (Order.coheight x : WithBot ℕ∞) := by
  rw [topologicalKrullDim,
    Order.krullDim_eq_of_orderIso (irreducibleSetEquivPoints (α := T)),
    Order.krullDim_eq_iSup_coheight]

/-- Each point coheight is bounded by the dimension of the ambient sober space. -/
theorem coheight_le_topologicalKrullDim (x : T) :
    (Order.coheight x : WithBot ℕ∞) ≤ topologicalKrullDim T := by
  rw [topologicalKrullDim_eq_iSup_coheight]
  exact le_iSup (fun y : T ↦ (Order.coheight y : WithBot ℕ∞)) x

/-- An upper bound on dimension can be checked on open neighborhoods. -/
theorem topologicalKrullDim_le_of_open_cover (d : WithBot ℕ∞)
    (h : ∀ x : T, ∃ U : Opens T, x ∈ U ∧ topologicalKrullDim U ≤ d) :
    topologicalKrullDim T ≤ d := by
  rw [topologicalKrullDim_eq_iSup_coheight]
  refine iSup_le fun x ↦ ?_
  obtain ⟨U, hx, hU⟩ := h x
  have : QuasiSober U := U.isOpenEmbedding'.quasiSober
  have he := U.isOpenEmbedding'.coheight_eq (x := (⟨x, hx⟩ : U))
  have hd := coheight_le_topologicalKrullDim (⟨x, hx⟩ : U)
  rw [← he] at hd
  exact hd.trans hU

/-- A nonempty space covered by opens of the same dimension has that dimension. -/
theorem topologicalKrullDim_eq_of_open_cover [Nonempty T] (d : WithBot ℕ∞)
    (h : ∀ x : T, ∃ U : Opens T, x ∈ U ∧ topologicalKrullDim U = d) :
    topologicalKrullDim T = d := by
  refine le_antisymm (topologicalKrullDim_le_of_open_cover d fun x ↦ ?_) ?_
  · obtain ⟨U, hx, hU⟩ := h x
    exact ⟨U, hx, hU.le⟩
  · obtain ⟨x⟩ := ‹Nonempty T›
    obtain ⟨U, _, hU⟩ := h x
    rw [← hU]
    exact topologicalKrullDim_subspace_le T U

end Topology

/-- The dimension of an affine open is the Krull dimension of its sections. -/
theorem topologicalKrullDim_affineOpen {X : Scheme.{u}} (U : X.Opens)
    (hU : IsAffineOpen U) : topologicalKrullDim U = ringKrullDim Γ(X, U) := by
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact hU.isoSpec.hom.homeomorph.isHomeomorph.topologicalKrullDim_eq _

/-- Every point of a smooth scheme over a field has a nonempty affine chart whose
sections are standard smooth over that same field, of the prescribed dimension. -/
theorem exists_standardSmooth_affine_chart {K : Type u} [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) [SmoothOfRelativeDimension n f]
    (x : X) : ∃ (V : X.Opens) (_ : IsAffineOpen V), x ∈ V ∧
      Nontrivial Γ(X, V) ∧ ∃ g : K →+* Γ(X, V),
        RingHom.IsStandardSmoothOfRelativeDimension n g := by
  obtain ⟨U, _, V, hV, hx, e, hg⟩ :=
    SmoothOfRelativeDimension.exists_isStandardSmoothOfRelativeDimension
      (n := n) (f := f) x
  have hU : U = ⊤ := by
    apply top_unique
    intro y _
    have hy : y = f x := Subsingleton.elim _ _
    exact hy ▸ e hx
  subst U
  let g := (f.appLE ⊤ V e).hom
  let i := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv
  refine ⟨V, hV, hx, (hV.primeIdealOf ⟨x, hx⟩).nontrivial,
    g.comp i.symm.toRingHom, ?_⟩
  exact RingHom.isStandardSmoothOfRelativeDimension_respectsIso.right g i.symm hg

/-- The scheme part of FC12: the only additional input is the dimension theorem
for nonzero standard-smooth algebras over a field. -/
theorem smoothCurveDimension_of_standardSmooth_dimension
    (K : Type u) [Field K]
    (halg : ∀ (A : Type u) [CommRing A] [Nontrivial A]
      (g : K →+* A), RingHom.IsStandardSmoothOfRelativeDimension 1 g →
        ringKrullDim A = 1)
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) :
    SmoothCurveDimension f := by
  intro hs hn
  apply topologicalKrullDim_eq_of_open_cover 1
  intro x
  obtain ⟨V, hV, hx, hne, g, hg⟩ := exists_standardSmooth_affine_chart f 1 x
  refine ⟨V, hx, ?_⟩
  exact (topologicalKrullDim_affineOpen V hV).trans (halg Γ(X, V) g hg)

end FLT.Mazur.FCurve
