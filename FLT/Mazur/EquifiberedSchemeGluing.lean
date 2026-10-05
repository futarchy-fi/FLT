/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import Mathlib.AlgebraicGeometry.RelativeGluing

/-!
# Cartesian charts for equifibered scheme gluing

An equifibered transformation of locally directed open diagrams induces a
map of glued schemes whose chart squares are pullbacks. The statement uses
the chosen colimits, so it can also be transported to explicit glue data.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u v

variable {J : Type v} [SmallCategory J] [Small.{u} J] [Quiver.IsThin J]
  {F G : J ⥤ Scheme.{u}}
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (F.map f)]
  [∀ {i j} (f : i ⟶ j), IsOpenImmersion (G.map f)]
  [(F ⋙ Scheme.forget).IsLocallyDirected] [(G ⋙ Scheme.forget).IsLocallyDirected]
  (s : F ⟶ G) (hs : s.Equifibered)

include hs in
/-- The preimage of a chart under the glued map is exactly its source chart. -/
theorem equifibered_colimit_preimage (i : J) :
    colimMap s ⁻¹' Set.range (colimit.ι G i) = Set.range (colimit.ι F i) := by
  ext x
  constructor
  · rintro ⟨y, hy⟩
    obtain ⟨j, xj, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective F x
    have heq : colimit.ι G i y = colimit.ι G j (s.app j xj) := by
      simpa only [← Scheme.Hom.comp_apply, ι_colimMap] using hy
    obtain ⟨k, fi, fj, z, hz, hj⟩ :=
      (Scheme.IsLocallyDirected.ι_eq_ι_iff G).mp heq
    obtain ⟨w, hw, hx⟩ := Scheme.exists_preimage_of_isPullback (hs fj) xj z hj.symm
    refine ⟨F.map fi w, ?_⟩
    rw [← Scheme.Hom.comp_apply, colimit.w]
    rw [← hw, ← Scheme.Hom.comp_apply, colimit.w]
  · rintro ⟨y, rfl⟩
    refine ⟨s.app i y, ?_⟩
    simp only [← Scheme.Hom.comp_apply, ι_colimMap]

include hs in
/-- Every chart square of the map of colimits is cartesian. -/
theorem equifibered_colimit_isPullback (i : J) :
    IsPullback (s.app i) (colimit.ι F i) (colimit.ι G i) (colimMap s) := by
  refine ⟨by simp, ⟨PullbackCone.IsLimit.mk _ ?_ ?_ ?_ ?_⟩⟩
  · intro c
    apply IsOpenImmersion.lift (colimit.ι F i) c.snd
    rw [← equifibered_colimit_preimage s hs]
    rintro x ⟨y, rfl⟩
    use c.fst y
    simp only [← Scheme.Hom.comp_apply, c.condition]
  · intro c
    rw [← cancel_mono (colimit.ι G i), Category.assoc, ← ι_colimMap,
      IsOpenImmersion.lift_fac_assoc, c.condition]
  · simp
  · intro c m h1 h2
    simpa [← cancel_mono (colimit.ι F i)]

end FLT.Mazur.Approximation
