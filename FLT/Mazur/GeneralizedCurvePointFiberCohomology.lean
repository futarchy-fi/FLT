/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.GeneralizedCurveGeometricPointPowers
public import FLT.Mazur.GeneralizedCurveMarkingBaseChange
public import FLT.Mazur.ProperLineGeometricFieldTests

/-!
# Original smooth-marking pole cohomology on every field fiber

The computed geometric cohomology applies to the actual pulled-back coefficient.
Algebraic-closure descent then gives every field fiber, retaining the original
family, marking, and scalar action, with no restriction on the base.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory
namespace FLT.Mazur.GeneralizedEllipticCurve
open FCurve GroupSectionBaseChange
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {S : Scheme} (E : GeneralizedEllipticCurve S)
  (s : 𝟙_ (Over S) ⟶ E.group) (m : ℕ) (hm : 0 < m)

include hm

/-- The actual original coefficient has vanishing positive cohomology on geometric fibers. -/
theorem smoothMarkingPower_geometricFiber_acyclic {K : Type} [Field K] [IsAlgClosed K]
    (g : Spec (.of K) ⟶ S) (r : ℕ) :
    Subsingleton (ModuleH ((Scheme.Modules.pullback (pullback.fst E.curve.hom g)).obj
      (E.smoothMarkingPower s m)) (r + 1)) := by
  let _ := (E.baseChange g).smoothMarkingPower_geometric_acyclic (pullSection g s) m hm r
  exact moduleH_subsingleton_of_iso (E.smoothMarkingPowerBaseChangeIso g s m) (r + 1)

/-- The original coefficient has the expected dimension on every geometric fiber. -/
theorem smoothMarkingPower_geometricFiber_h0 {K : Type} [Field K] [IsAlgClosed K]
    (g : Spec (.of K) ⟶ S) :
    Module.finrank K (ModuleScalarH (pullback.snd E.curve.hom g)
      ((Scheme.Modules.pullback (pullback.fst E.curve.hom g)).obj
        (E.smoothMarkingPower s m)) 0) = m :=
  ((moduleScalarHFunctor (pullback.snd E.curve.hom g) 0).mapIso
    (E.smoothMarkingPowerBaseChangeIso g s m)).toLinearEquiv.finrank_eq.trans
      ((E.baseChange g).smoothMarkingPower_geometric_h0 (pullSection g s) m hm)

/-- Every field-valued fiber has the same actual acyclic positive pole coefficient. -/
theorem smoothMarkingPower_fieldFiber_acyclic {K : Type} [Field K]
    (g : Spec (.of K) ⟶ S) (r : ℕ) :
    Subsingleton (ModuleH ((Scheme.Modules.pullback (pullback.fst E.curve.hom g)).obj
      (E.smoothMarkingPower s m)) (r + 1)) := by
  let _ : IsProper E.curve.hom := E.family.family.1
  exact properLine_field_vanishing_of_geometric E.curve.hom _
    (E.smoothMarkingPower_rankOne s m) (r + 1)
    (fun _ _ _ g ↦ E.smoothMarkingPower_geometricFiber_acyclic s m hm g r) g

/-- Every field-valued fiber has exactly m sections in positive pole degree m. -/
theorem smoothMarkingPower_fieldFiber_h0 {K : Type} [Field K]
    (g : Spec (.of K) ⟶ S) :
    Module.finrank K (ModuleScalarH (pullback.snd E.curve.hom g)
      ((Scheme.Modules.pullback (pullback.fst E.curve.hom g)).obj
        (E.smoothMarkingPower s m)) 0) = m := by
  let _ : IsProper E.curve.hom := E.family.family.1
  exact properLine_field_finrank_of_geometric E.curve.hom _
    (E.smoothMarkingPower_rankOne s m) 0 m
    (fun _ _ _ g ↦ E.smoothMarkingPower_geometricFiber_h0 s m hm g) g

end FLT.Mazur.GeneralizedEllipticCurve
