/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import Mathlib.AlgebraicGeometry.ZariskisMainTheorem
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant

/-!
# Finiteness from finitely many sections containing a dense image

In a separated scheme the images of sections are closed. If finitely many such
images contain a dense subset, they cover the whole scheme and every fiber is
finite. Properness then gives a finite morphism.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

namespace FLT.Mazur.ProperDenseFiniteSections

universe u v
variable {X S T : Scheme.{u}} (f : X ⟶ S)
  {I : Type v} [Finite I] (s : I → (S ⟶ X)) (hs : ∀ j, s j ≫ f = 𝟙 S)

include hs

omit [Finite I] in
/-- An actual section of the separated structural map is a closed immersion. -/
theorem section_closed [IsSeparated f] (j : I) : IsClosedImmersion (s j) := by
  let _ : IsClosedImmersion (s j ≫ f) := by rw [hs j]; infer_instance
  exact IsClosedImmersion.of_comp (s j) f

/-- A finite union of section images containing a dense image covers the entire scheme. -/
theorem sections_cover [IsSeparated f] (a : T ⟶ X) (ha : DenseRange a)
    (hcover : ∀ x : T, ∃ j : I, a x ∈ Set.range (s j)) (x : X) :
    ∃ j : I, x ∈ Set.range (s j) := by
  have hc : IsClosed (⋃ j, Set.range (s j)) := by
    apply isClosed_iUnion_of_finite
    intro j
    let _ := section_closed f s hs j
    exact (s j).isClosedEmbedding.isClosed_range
  have hx : x ∈ ⋃ j, Set.range (s j) := ha.induction_on x hc (fun y => by
    obtain ⟨j, hj⟩ := hcover y
    exact Set.mem_iUnion.mpr ⟨j, hj⟩)
  exact Set.mem_iUnion.mp hx

/-- The finitely many sections explicitly bound each fiber by their values at its base point. -/
theorem finite_fiber (hcover : ∀ x : X, ∃ j : I, x ∈ Set.range (s j)) (y : S) :
    (f ⁻¹' {y}).Finite := by
  apply (Set.finite_range fun j => s j y).subset
  intro x hx
  obtain ⟨j, z, rfl⟩ := hcover x
  have hz : z = y := by
    have he := congrArg (fun g : S ⟶ S => g z) (hs j)
    exact he.symm.trans hx
  exact ⟨j, by rw [hz]⟩

/-- A proper scheme covered by finitely many section images is finite over the base. -/
theorem finite_of_sections [IsProper f]
    (hcover : ∀ x : X, ∃ j : I, x ∈ Set.range (s j)) : IsFinite f := by
  let _ : LocallyQuasiFinite f :=
    LocallyQuasiFinite.of_finite_preimage_singleton f (finite_fiber f s hs hcover)
  exact IsFinite.of_isProper_of_locallyQuasiFinite f

/-- A dense generic source contained in finitely many integral sections forces finiteness. -/
theorem finite_of_dense_sections [IsProper f] (a : T ⟶ X) (ha : DenseRange a)
    (hcover : ∀ x : T, ∃ j : I, a x ∈ Set.range (s j)) : IsFinite f :=
  finite_of_sections f s hs (sections_cover f s hs a ha hcover)

end FLT.Mazur.ProperDenseFiniteSections
