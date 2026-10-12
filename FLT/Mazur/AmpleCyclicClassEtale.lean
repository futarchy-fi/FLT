/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AmpleCyclicClassPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.Etale

/-!
# The intrinsic etale-subgroup condition on ample cyclic classes

Etaleness concerns the actual finite subgroup scheme, so compatible isomorphism
preserves it. This gives a class predicate stable under arbitrary base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {S T : Scheme} {n : ℕ} {E F : GeneralizedEllipticCurve S}
  {H : E.FiniteSubgroup n} {J : F.FiniteSubgroup n}

/-- Compatible isomorphisms preserve etaleness of the actual finite subgroup. -/
theorem CompatibleIso.etale_iff (a : CompatibleIso H J) :
    Etale H.carrier.hom ↔ Etale J.carrier.hom := by
  have : IsIso a.subgroup.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S).mapIso a.subgroup).hom)
  rw [← a.subgroup.hom.w, MorphismProperty.cancel_left_of_respectsIso (P := @Etale)]

/-- The subgroup-etale condition is an intrinsic property of ample cyclic classes. -/
def ampleCyclicClassEtale (q : ampleCyclicClasses S n) : Prop :=
  Quotient.lift (s := ampleCyclicLevelSetoid S n)
    (fun a : ampleCyclicLevels S n ↦ Etale a.val.2.carrier.hom)
    (fun _ _ ⟨a⟩ ↦ propext a.etale_iff) q

/-- On a represented level the class predicate is exactly etaleness of its subgroup. -/
theorem ampleCyclicClassEtale_mk (a : ampleCyclicLevels S n) :
    ampleCyclicClassEtale (Quotient.mk _ a) ↔ Etale a.val.2.carrier.hom := Iff.rfl

/-- Etale cyclic-subgroup classes remain etale after every base change. -/
theorem ampleCyclicClassEtale_pullback (g : T ⟶ S) (q : ampleCyclicClasses S n)
    (hq : ampleCyclicClassEtale q) :
    ampleCyclicClassEtale (ampleCyclicClassesPullback g n q) := by
  induction q using Quotient.inductionOn with
  | h a =>
    change Etale a.val.2.carrier.hom at hq
    let _ := hq
    change Etale (CategoryTheory.Limits.pullback.snd a.val.2.carrier.hom g)
    infer_instance

end FLT.Mazur.GeneralizedEllipticCurve.FiniteSubgroup
