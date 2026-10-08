/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleFiberAffineNeighborhood
public import FLT.Mazur.AmpleFiberBaseChange
public import FLT.Mazur.ProperAmpleConverse

/-!
# An ample fiber spreads over a locally Noetherian base

Properness supplies compactness and separatedness over affine base charts.
The affine result then descends from the chosen chart to an actual affine
open of the original base, with a closed projective power presentation.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry
open Scheme.Modules

namespace FLT.Mazur.FCurve

/-- Over an affine Noetherian base, properness supplies the auxiliary space hypotheses. -/
theorem exists_ample_neighborhood_affine_noetherian {X S : Scheme.{0}}
    [IsAffine S] [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f] (s : S)
    {L : X.Modules} (hline : LocallyFreeRankOne L)
    (hL : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ V : S.Opens, s ∈ V ∧ IsAffineOpen V ∧
      AmpleLineBundle ((pullback (f ⁻¹ᵁ V).ι).obj L) := by
  let _ : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  let _ : X.IsSeparated := ⟨by rw [← Limits.terminal.comp_from f]; infer_instance⟩
  exact StalkBase.exists_ample_affine_neighborhood f s hline hL

/-- A proper family over any locally Noetherian base is ample near each ample fiber. -/
theorem exists_ample_neighborhood_locally_noetherian {X S : Scheme.{0}}
    [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f] (s : S)
    {L : X.Modules} (hline : LocallyFreeRankOne L)
    (hL : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧
      AmpleLineBundle ((pullback (f ⁻¹ᵁ W).ι).obj L) := by
  obtain ⟨V, hV, hsV, _⟩ := exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens)
    from trivial)
  let _ : IsAffine V.toScheme := hV
  have ha := ampleLineBundle_fiber_morphismRestrict f V ⟨s, hsV⟩ L hL
  obtain ⟨U, hsU, hU, hA⟩ := exists_ample_neighborhood_affine_noetherian
    (f ∣_ V) ⟨s, hsV⟩ (hline.pullback _) ha
  let _ : IsAffine U.toScheme := hU
  exact ⟨V.ι ''ᵁ U, ⟨⟨s, hsV⟩, hsU, rfl⟩, .of_isIso (V.ι.isoImage U).inv,
    ampleLineBundle_baseOpenImage f V U L hA⟩

/-- The neighborhood carries the closed-power-presentation relative ample predicate. -/
theorem exists_relativeAmple_neighborhood_locally_noetherian {X S : Scheme.{0}}
    [IsLocallyNoetherian S] (f : X ⟶ S) [IsProper f] (s : S)
    {L : X.Modules} (hline : LocallyFreeRankOne L)
    (hL : AmpleLineBundle ((pullback (f.fiberι s)).obj L)) :
    ∃ W : S.Opens, s ∈ W ∧ IsAffineOpen W ∧
      RelativeAmple (f ∣_ W) ((pullback (f ⁻¹ᵁ W).ι).obj L) := by
  obtain ⟨W, hsW, hW, hA⟩ :=
    exists_ample_neighborhood_locally_noetherian f s hline hL
  let _ : IsAffine W.toScheme := hW
  exact ⟨W, hsW, hW, (hA.relative_of_affine (f ∣_ W)).relativeAmple⟩

end FLT.Mazur.FCurve
