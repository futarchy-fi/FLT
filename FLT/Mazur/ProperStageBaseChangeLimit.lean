/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeClosedBaseChange
public import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Fiber limits above a proper stage

In a closed inverse system over a fixed base, every refinement of a proper
stage is proper. After any fixed base change the restricted diagram retains
its limit and closed transitions; a qcqs base makes all its terms qcqs.
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry

namespace FLT.Mazur.Approximation

universe u

variable {I : Type u} [Category.{u} I] [IsCofiltered I]
  {S Y : Scheme.{u}} {D : I ⥤ Scheme.{u}}
  (t : D ⟶ (Functor.const I).obj S) (q : Y ⟶ S) (i : I)

/-- Base change of the subsystem consisting of all refinements of a fixed stage. -/
def properStageBaseChangeDiagram : Over i ⥤ Scheme.{u} :=
  schemeBaseChangeDiagram ((Over.forget i).whiskerLeft t) q

/-- The fixed base change of the original limit cones over the refinement subsystem. -/
def properStageBaseChangeCone (c : Cone D) (b : c.pt ⟶ S)
    (hb : ∀ j, c.π.app j ≫ t.app j = b) : Cone (properStageBaseChangeDiagram t q i) :=
  schemeBaseChangeCone ((Over.forget i).whiskerLeft t) q
    (c.whisker (Over.forget i)) b (fun j ↦ hb j.left)

/-- Restricting above a stage and then base changing preserves the actual inverse limit. -/
def properStageBaseChangeIsLimit (c : Cone D) (hc : IsLimit c) (b : c.pt ⟶ S)
    (hb : ∀ j, c.π.app j ≫ t.app j = b) :
    IsLimit (properStageBaseChangeCone t q i c b hb) := by
  let _ := IsCofiltered.isConnected (Over i)
  exact schemeBaseChangeIsLimit ((Over.forget i).whiskerLeft t) q
    (c.whisker (Over.forget i)) b (fun j ↦ hb j.left)
    ((Functor.Initial.isLimitWhiskerEquiv (Over.forget i) c).symm hc)

variable [∀ {j k} (f : j ⟶ k), IsClosedImmersion (D.map f)] [IsProper (t.app i)]

/-- Every fiber stage above the chosen proper stage is proper over the new base. -/
instance properStageBaseChangeDiagram_isProper (j : Over i) :
    IsProper (pullback.fst q (t.app j.left)) := by
  have he : D.map j.hom ≫ t.app i = t.app j.left :=
    (t.naturality j.hom).trans (Category.comp_id _)
  let _ : IsProper (t.app j.left) := he ▸
    (inferInstance : IsProper (D.map j.hom ≫ t.app i))
  infer_instance

/-- Base-changed refinements retain their closed-immersion transitions. -/
instance properStageBaseChangeDiagram_closed {j k : Over i} (f : j ⟶ k) :
    IsClosedImmersion ((properStageBaseChangeDiagram t q i).map f) := by
  let _ {j k : Over i} (f : j ⟶ k) :
      IsClosedImmersion ((Over.forget i ⋙ D).map f) :=
    inferInstanceAs (IsClosedImmersion (D.map f.left))
  exact schemeBaseChangeDiagram_map_isClosedImmersion ((Over.forget i).whiskerLeft t) q f

/-- A quasi-separated base makes all the proper fiber stages quasi-separated. -/
instance properStageBaseChangeDiagram_quasiSeparatedSpace [QuasiSeparatedSpace Y]
    (j : Over i) : QuasiSeparatedSpace ((properStageBaseChangeDiagram t q i).obj j) := by
  let _ : IsProper (pullback.fst q (t.app j.left)) :=
    properStageBaseChangeDiagram_isProper t q i j
  exact quasiSeparatedSpace_of_quasiSeparated (X := pullback q (t.app j.left))
    (pullback.fst q (t.app j.left))

/-- A compact base makes all the proper fiber stages compact. -/
instance properStageBaseChangeDiagram_compactSpace [CompactSpace Y] (j : Over i) :
    CompactSpace ((properStageBaseChangeDiagram t q i).obj j) := by
  let _ : IsProper (pullback.fst q (t.app j.left)) :=
    properStageBaseChangeDiagram_isProper t q i j
  exact QuasiCompact.compactSpace_of_compactSpace (X := pullback q (t.app j.left))
    (pullback.fst q (t.app j.left))

end FLT.Mazur.Approximation
