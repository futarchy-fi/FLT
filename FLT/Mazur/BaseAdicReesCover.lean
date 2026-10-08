/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSpace
public import Mathlib.AlgebraicGeometry.PullbackCarrier

/-!
# Coverage by the actual relative Rees charts

Each tensor chart has exactly the inverse image of its original affine open
as its range. Consequently these charts cover the actual base change.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)
  (J : Ideal R) (V : X.affineOpens)

/-- The pullback chart lies over exactly its original affine open. -/
lemma chartPullbackMap_range :
    Set.range (chartPullbackMap f J V) = pullback.fst f (baseMap J) ⁻¹' V.1 := by
  rw [chartPullbackMap, Scheme.Pullback.range_map]
  change (pullback.fst f (baseMap J) ⁻¹' Set.range V.2.fromSpec) ∩
    (pullback.snd f (baseMap J) ⁻¹' Set.range id) = _
  rw [V.2.range_fromSpec, Set.range_id, Set.preimage_univ, Set.inter_univ]

/-- Tensor coordinates do not change the image of the affine pullback chart. -/
lemma chartSpaceMap_range :
    let _ := chartAlgebra f V
    Set.range (chartSpaceMap f J V) = pullback.fst f (baseMap J) ⁻¹' V.1 := by
  let _ := chartAlgebra f V
  have hr : Set.range (chartSpaceMap f J V) = Set.range (chartPullbackMap f J V) := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      exact ⟨(pullbackSpecIso R Γ(X, V.1) (reesAlgebra J)).inv y, rfl⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨z, rfl⟩ :=
        (pullbackSpecIso R Γ(X, V.1) (reesAlgebra J)).inv.homeomorph.surjective y
      exact ⟨z, rfl⟩
  exact hr.trans (chartPullbackMap_range f J V)

/-- The tensor chart's open range is the inverse image of the source chart. -/
lemma chartSpaceMap_opensRange :
    let _ := chartAlgebra f V
    (chartSpaceMap f J V).opensRange = pullback.fst f (baseMap J) ⁻¹ᵁ V.1 := by
  let _ := chartAlgebra f V
  exact TopologicalSpace.Opens.ext (chartSpaceMap_range f J V)

/-- Every point of the actual relative Rees space has tensor chart coordinates. -/
theorem chartSpaceMap_covers (x : relativeSpace f J) :
    ∃ V : X.affineOpens, x ∈ Set.range (chartSpaceMap f J V) := by
  obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := X) (x := pullback.fst f (baseMap J) x) (U := ⊤) trivial
  exact ⟨⟨V, hV⟩, (chartSpaceMap_range f J ⟨V, hV⟩).symm ▸ hx⟩

/-- The original affine charts provide an open cover of the actual base change. -/
def chartCover : (relativeSpace f J).OpenCover where
  I₀ := X.affineOpens
  X V := let _ := chartAlgebra f V
    Spec (.of (Γ(X, V.1) ⊗[R] reesAlgebra J))
  f V := chartSpaceMap f J V
  mem₀ := by
    rw [Scheme.ofArrows_mem_precoverage_iff]
    exact ⟨chartSpaceMap_covers f J, fun _ ↦ inferInstance⟩

end FLT.Mazur.BaseAdicRees
