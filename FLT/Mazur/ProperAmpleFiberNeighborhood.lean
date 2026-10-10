/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleFiberBaseIso
public import FLT.Mazur.ProperAmpleFiberApproximation

/-!
# Ample fiber neighborhoods for proper finitely presented families

No Noetherian hypothesis is imposed on the base. Affine charts reduce to
the approximation theorem over spectra, and open-image transport returns
the neighborhood on the original base. This does not remove the finite
presentation hypothesis required by the approximation input.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.FCurve

/-- Spread an ample fiber over an arbitrary affine base using finite presentation. -/
theorem exists_ample_neighborhood_affine_finitePresentation {X S : Scheme.{0}}
    [IsAffine S] (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    (s : S) (L : X.Modules) (hL : LocallyFreeRankOne L)
    (hA : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧
      AmpleLineBundle ((pullback (f ⁻¹ᵁ V).ι).obj L) := by
  let q := f ≫ S.isoSpec.hom
  have hF := ampleLineBundle_fiber_baseIso f S.isoSpec s L hA
  obtain ⟨U, hsU, hU, ha⟩ :=
    exists_ample_neighborhood_spectrum q L hL (S.isoSpec.hom s) hF
  refine ⟨S.isoSpec.hom ⁻¹ᵁ U, hsU, hU.preimage S.isoSpec.hom, ?_⟩
  simpa only [q, Scheme.Hom.comp_preimage] using ha

/-- A proper finitely presented family has an ample neighborhood of every ample fiber. -/
theorem exists_ample_neighborhood_finitePresentation {X S : Scheme.{0}}
    (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    (s : S) (L : X.Modules) (hL : LocallyFreeRankOne L)
    (hA : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧
      AmpleLineBundle ((pullback (f ⁻¹ᵁ W).ι).obj L) := by
  obtain ⟨V, hV, hsV, _⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens)
    from trivial)
  let _ : IsAffine V.toScheme := hV
  have ha := ampleLineBundle_fiber_morphismRestrict f V ⟨s, hsV⟩ L hA
  obtain ⟨U, hsU, hU, hB⟩ := exists_ample_neighborhood_affine_finitePresentation
    (f ∣_ V) ⟨s, hsV⟩ ((pullback (f ⁻¹ᵁ V).ι).obj L) (hL.pullback _) ha
  let _ : IsAffine U.toScheme := hU
  exact ⟨V.ι ''ᵁ U, ⟨⟨s, hsV⟩, hsU, rfl⟩, .of_isIso (V.ι.isoImage U).inv,
    ampleLineBundle_baseOpenImage f V U L hB⟩

/-- The original line admits relative closed power presentations near an ample fiber. -/
theorem exists_relativeAmple_neighborhood_finitePresentation {X S : Scheme.{0}}
    (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    (s : S) (L : X.Modules) (hL : LocallyFreeRankOne L)
    (hA : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧
      RelativeAmple (f ∣_ W) (L.restrict (f ⁻¹ᵁ W).ι) := by
  obtain ⟨W, hsW, hW, ha⟩ := exists_ample_neighborhood_finitePresentation f s L hL hA
  let _ : IsAffine W.toScheme := hW
  have hb := ha.of_iso ((restrictFunctorIsoPullback (f ⁻¹ᵁ W).ι).app L)
  exact ⟨W, hsW, hW, (hb.relative_of_affine (f ∣_ W)).relativeAmple⟩

/-- Fiberwise ampleness is relative ampleness for a proper finitely presented family. -/
theorem relativeAmple_of_ample_fibers_finitePresentation {X S : Scheme.{0}}
    (f : X ⟶ S) [IsProper f] [LocallyOfFinitePresentation f]
    (L : X.Modules) (hL : LocallyFreeRankOne L)
    (hA : ∀ s : S, AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    RelativeAmple f L := by
  apply relativeAmple_of_base_neighborhoods hL
  intro s
  obtain ⟨W, hsW, _, ha⟩ :=
    exists_relativeAmple_neighborhood_finitePresentation f s L hL (hA s)
  exact ⟨W, hsW, ha⟩

end FLT.Mazur.FCurve
