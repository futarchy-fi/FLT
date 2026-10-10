/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedImmersionLimitDescent
public import FLT.Mazur.SchemeClosedBaseChange

/-!
# Closedness of a fixed cover map along a closed inverse system

Pulling a fixed cover back to a closed inverse system preserves its limit.
Closedness of its map to a compact ambient scheme descends to one stage.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  (D : I ⥤ Scheme.{u}) (c : Cone D) (hc : IsLimit c)
  [∀ {i j} (g : i ⟶ j), IsClosedImmersion (D.map g)]

include hc in
/-- Closedness of the pulled-back cover map holds at some finite stage. -/
theorem exists_isClosedImmersion_cover_map {X Z P : Scheme.{u}}
    [QuasiSeparatedSpace Z] [CompactSpace P]
    (t : D ⟶ (Functor.const I).obj X) [∀ i, IsClosedImmersion (t.app i)]
    (b : c.pt ⟶ X) (hb : ∀ i, c.π.app i ≫ t.app i = b)
    (q : Z ⟶ X) (h : Z ⟶ P) [QuasiCompact h] [LocallyOfFiniteType h]
    (hh : IsClosedImmersion (pullback.fst q b ≫ h)) :
    ∃ i, IsClosedImmersion (pullback.fst q (t.app i) ≫ h) := by
  let _ := IsCofiltered.isConnected I
  let F := schemeBaseChangeDiagram t q
  let d := schemeBaseChangeCone t q c b hb
  let _ (i : I) : QuasiSeparatedSpace (F.obj i) :=
    schemeBaseChangeDiagram_quasiSeparatedSpace t q i
  let _ (i : I) : IsClosedImmersion (pullback.fst q (t.app i)) :=
    MorphismProperty.pullback_fst _ _ (inferInstanceAs (IsClosedImmersion (t.app i)))
  let i : I := Classical.choice (IsCofiltered.nonempty (C := I))
  let g : F.obj i ⟶ P := pullback.fst q (t.app i) ≫ h
  have he : d.π.app i ≫ g = pullback.fst q b ≫ h := by
    simp [d, g, schemeBaseChangeCone]
  let _ : IsClosedImmersion (d.π.app i ≫ g) := he.symm ▸ hh
  obtain ⟨j, r, hj⟩ := exists_isClosedImmersion_of_closed_limit F d
    (schemeBaseChangeIsLimit t q c b hb hc) i g
  refine ⟨j, ?_⟩
  have hn : F.map r ≫ g = pullback.fst q (t.app j) ≫ h := by
    simp [F, g, schemeBaseChangeDiagram]
  exact (congrArg (fun k ↦ IsClosedImmersion k) hn).mp hj

end FLT.Mazur.Approximation
