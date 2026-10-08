/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.BaseAdicReesSheafMap

/-!
# Common principal refinements of relative Rees charts

Common principal opens on the original scheme cover the relative chart
intersections and the source of every affine chart inclusion.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory Limits AlgebraicGeometry
open scoped TensorProduct

universe u

namespace FLT.Mazur.BaseAdicRees

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R) (J : Ideal R)

/-- Relative chart membership is detected on the original scheme. -/
lemma chartSpaceMap_mem_range_iff (U : X.affineOpens) (x : relativeSpace f J) :
    x ∈ Set.range (chartSpaceMap f J U) ↔ pullback.fst f (baseMap J) x ∈ U.1 := by
  rw [chartSpaceMap_range]
  rfl

/-- Each pairwise chart intersection is covered by common principal relative charts. -/
lemma chartSpaceMap_exists_common_principal (U V : X.affineOpens)
    (x : relativeSpace f J) (hU : x ∈ Set.range (chartSpaceMap f J U))
    (hV : x ∈ Set.range (chartSpaceMap f J V)) :
    ∃ (r : Γ(X, U.1)) (s : Γ(X, V.1)), X.basicOpen r = X.basicOpen s ∧
      x ∈ Set.range (chartSpaceMap f J ⟨X.basicOpen r, U.2.basicOpen r⟩) := by
  obtain ⟨r, s, hrs, hx⟩ := exists_basicOpen_le_affine_inter U.2 V.2
    (pullback.fst f (baseMap J) x)
    ⟨(chartSpaceMap_mem_range_iff f J U x).mp hU,
      (chartSpaceMap_mem_range_iff f J V x).mp hV⟩
  exact ⟨r, s, hrs, (chartSpaceMap_mem_range_iff f J _ x).mpr hx⟩

/-- Membership in a model inclusion is detected after its chart open immersion. -/
lemma modelMap_mem_range_iff {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f V
    ∀ x : Spec (.of (Γ(X, V.1) ⊗[R] reesAlgebra J)),
      x ∈ Set.range (modelMap f J h) ↔
        chartSpaceMap f J V x ∈ Set.range (chartSpaceMap f J U) := by
  intro _ x
  change x ∈ Set.range
    (Spec.map (CommRingCat.ofHom (relativeRingRestriction f J h).toRingHom)) ↔ _
  rw [relativeRingRestriction_range, chartSpaceMap_range]
  rfl

/-- Common principal refinements cover the source of every model inclusion. -/
lemma modelMap_exists_common_principal {U V : X.affineOpens} (h : U.1 ≤ V.1) :
    let _ := chartAlgebra f U
    ∀ x : Spec (.of (Γ(X, U.1) ⊗[R] reesAlgebra J)),
      ∃ (r : Γ(X, U.1)) (s : Γ(X, V.1)), X.basicOpen r = X.basicOpen s ∧
        x ∈ Set.range (modelMap f J (U := ⟨X.basicOpen r, U.2.basicOpen r⟩)
          (V := U) (X.basicOpen_le r)) := by
  intro _ x
  have hxV : chartSpaceMap f J U x ∈ Set.range (chartSpaceMap f J V) := by
    refine ⟨modelMap f J h x, ?_⟩
    exact congrArg (fun g ↦ g x) (relativeRingRestriction_spec f J h)
  obtain ⟨r, s, hrs, hx⟩ := chartSpaceMap_exists_common_principal f J U V
    (chartSpaceMap f J U x) ⟨x, rfl⟩ hxV
  exact ⟨r, s, hrs, (modelMap_mem_range_iff f J (U :=
    ⟨X.basicOpen r, U.2.basicOpen r⟩) (V := U) (X.basicOpen_le r) x).mpr hx⟩

end FLT.Mazur.BaseAdicRees
