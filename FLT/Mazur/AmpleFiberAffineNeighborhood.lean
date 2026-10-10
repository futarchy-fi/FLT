/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleFiberFiniteCoordinates
public import FLT.Mazur.AmpleOpenImage
public import FLT.Mazur.FiniteProjectiveSectionAmple

/-!
# Ampleness near one fiber over an affine Noetherian base

Finite projective coordinates give affine generator opens on a smaller
base neighborhood. Transport through the actual open-immersion images
returns an ample restriction over an open of the original base.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules FLT.Mazur.FCurve FLT.Mazur.ProjectiveSpace
open ModuleLineBundleTensorPullback

namespace FLT.Mazur.StalkBase

/-- A proper family with an ample fiber has an ample restriction near that fiber. -/
theorem exists_ample_affine_neighborhood {X S : Scheme.{0}}
    [IsAffine S] [IsLocallyNoetherian S] [CompactSpace X] [X.IsSeparated]
    (f : X ⟶ S) [IsProper f] (s : S) {L : X.Modules} (hline : LocallyFreeRankOne L)
    (hL : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧
      AmpleLineBundle ((pullback (f ⁻¹ᵁ W).ι).obj L) := by
  obtain ⟨V, hsV, hV, n, _, hn, d, t, ht, U, hsU, hU, hg⟩ :=
    exists_finite_projective_coordinate_neighborhood f s hline hL 0
  let _ : IsAffine V.toScheme := hV
  let _ : CompactSpace (f ⁻¹ᵁ V).toScheme :=
    QuasiCompact.compactSpace_of_compactSpace (f ∣_ V)
  let q := (f ∣_ V) ≫ hV.isoSpec.hom
  let L' := (pullback (f ⁻¹ᵁ V).ι).obj L
  let r := q.appTop.hom.comp (Scheme.ΓSpecIso Γ(S, V)).inv.hom
  have ha := ampleLineBundle_of_finite_sectionProjectiveMorphism
    (hline.pullback (f ⁻¹ᵁ V).ι) hn d t ht r U hU
  have he := congrArg (fun k ↦ k ⁻¹ᵁ U)
    (sectionProjectiveMorphism_baseProjection (tensorPower L' n) d t ht q)
  simp only [Scheme.Hom.comp_preimage] at he
  rw [he] at ha
  let U' := hV.isoSpec.hom ⁻¹ᵁ U
  have hU' : IsAffineOpen U' := hU.preimage hV.isoSpec.hom
  let _ : IsAffine U'.toScheme := hU'
  refine ⟨V.ι ''ᵁ U', ⟨⟨s, hsV⟩, hsU, rfl⟩,
    .of_isIso (V.ι.isoImage U').inv, ?_⟩
  apply ampleLineBundle_baseOpenImage f V U' L
  simpa only [q, Scheme.Hom.comp_preimage] using ha

end FLT.Mazur.StalkBase
