/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.RelativeAmpleFpqcDescent
public import Mathlib.AlgebraicGeometry.Fiber

/-!
# Ample fibers descend across a cartesian recovery square

The residue-field extension at a point is faithfully flat, even when the
base morphism is not. Thus ampleness of the recovered fiber descends to
the corresponding model fiber by the proved fpqc descent theorem.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace FLT.Mazur.FCurve

/-- A cartesian recovery square reflects ampleness at corresponding fibers.
No flatness or surjectivity of the original base morphism is required. -/
theorem relativeAmple_fiber_of_isPullback {X Y S T : Scheme.{0}}
    {a : X ⟶ Y} {p : X ⟶ T} {q : Y ⟶ S} {b : T ⟶ S}
    (sq : IsPullback a p q b) [IsProper q]
    {L : Y.Modules} (hL : LocallyFreeRankOne L) (t : T)
    (hA : RelativeAmple (p.fiberToSpecResidueField t)
      ((Scheme.Modules.pullback (p.fiberι t)).obj ((Scheme.Modules.pullback a).obj L))) :
    RelativeAmple (q.fiberToSpecResidueField (b t))
      ((Scheme.Modules.pullback (q.fiberι (b t))).obj L) := by
  let k := Spec.map (b.residueFieldMap t)
  have : Flat k := inferInstance
  have : Surjective k := ⟨Function.surjective_to_subsingleton k⟩
  have : QuasiCompact k := inferInstance
  let v : p.fiber t ⟶ q.fiber (b t) :=
    pullback.map _ _ _ _ a k b sq.w.symm (by simp [k])
  have hv : IsPullback v (p.fiberToSpecResidueField t)
      (q.fiberToSpecResidueField (b t)) k :=
    isPullback_fiberToSpecResidueField_of_isPullback sq t
  have hvι : v ≫ q.fiberι (b t) = p.fiberι t ≫ a := by
    simp [v, Scheme.Hom.fiberι]
  have e : (Scheme.Modules.pullback v).obj
      ((Scheme.Modules.pullback (q.fiberι (b t))).obj L) ≅
      (Scheme.Modules.pullback (p.fiberι t)).obj ((Scheme.Modules.pullback a).obj L) :=
    (Scheme.Modules.pullbackComp v (q.fiberι (b t))).app L ≪≫
      (Scheme.Modules.pullbackCongr hvι).app L ≪≫
      ((Scheme.Modules.pullbackComp (p.fiberι t) a).app L).symm
  have : IsProper (q.fiberToSpecResidueField (b t)) := by
    dsimp [Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  exact (hA.of_iso e).of_fpqc (hL.pullback _) hv

end FLT.Mazur.FCurve
