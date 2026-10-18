/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CyclicCharacteristicNormalizedSubgroup

/-!
# The genuine unmarked relation between normalized characteristic parameters

Parameters may belong to different characteristic charts. Relatedness means
an actual compatible isomorphism of the full curves and subgroup schemes,
with no auxiliary marking or generator required to agree. It is exactly
equality of the original ample cyclic modular classes and is stable under
arbitrary base change. Representability by a scheme is a separate question.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
namespace FLT.Mazur.CyclicCharacteristicAtlas
open GeneralizedEllipticCurve GeneralizedEllipticCurve.FiniteSubgroup
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable (n : ℕ) [NeZero n]

/-- The unmarked relation retains actual full-curve and subgroup isomorphisms. -/
def UnmarkedRelated {T : Scheme} (b c : Bool)
    (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c) : Prop :=
  Nonempty (CompatibleIso ((normalizedSubgroup n b).baseChange q)
    ((normalizedSubgroup n c).baseChange r))

/-- Genuine unmarked comparisons are exactly equality of the actual modular classes. -/
theorem unmarkedRelated_iff_moduli_eq {T : Scheme} (b c : Bool)
    (q : T ⟶ normalizedLocus n b) (r : T ⟶ normalizedLocus n c) :
    UnmarkedRelated n b c q r ↔
      (normalizedModuliMap n b).app (Opposite.op T) (ULift.up q) =
        (normalizedModuliMap n c).app (Opposite.op T) (ULift.up r) := by
  rw [normalizedModuliMap_eq_pullback, normalizedModuliMap_eq_pullback]
  constructor
  · intro h
    exact Quotient.sound h
  · intro h
    exact Quotient.exact h

/-- Every actual parameter is related to itself by the identity comparison. -/
theorem unmarkedRelated_refl {T : Scheme} (b : Bool) (q : T ⟶ normalizedLocus n b) :
    UnmarkedRelated n b b q q := ⟨CompatibleIso.refl _⟩

/-- Reversing the full compatible comparison reverses the unmarked relation. -/
theorem UnmarkedRelated.symm {T : Scheme} {b c : Bool}
    {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
    (h : UnmarkedRelated n b c q r) : UnmarkedRelated n c b r q :=
  h.map CompatibleIso.symm

/-- Compatible comparisons compose even when the middle chart has another characteristic. -/
theorem UnmarkedRelated.trans {T : Scheme} {b c d : Bool}
    {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
    {s : T ⟶ normalizedLocus n d}
    (h : UnmarkedRelated n b c q r) (k : UnmarkedRelated n c d r s) :
    UnmarkedRelated n b d q s := by
  obtain ⟨a⟩ := h
  obtain ⟨e⟩ := k
  exact ⟨a.trans e⟩

/-- Base change of the relation uses the original compatible isomorphism and canonical maps. -/
theorem UnmarkedRelated.baseChange {T U : Scheme} {b c : Bool}
    {q : T ⟶ normalizedLocus n b} {r : T ⟶ normalizedLocus n c}
    (h : UnmarkedRelated n b c q r) (g : U ⟶ T) :
    UnmarkedRelated n b c (g ≫ q) (g ≫ r) := by
  obtain ⟨a⟩ := h
  exact ⟨(compatibleBaseChangeComp (normalizedSubgroup n b) q g).trans
    ((a.baseChange g).trans (compatibleBaseChangeComp (normalizedSubgroup n c) r g).symm)⟩

/-- Every original relabeling is an actual unmarked comparison. -/
theorem unmarkedRelated_relabel {T : Scheme} (b : Bool)
    (q : T ⟶ normalizedLocus n b) (e : RelabelGroup n) :
    UnmarkedRelated n b b (q ≫ (normalizedRelabelAction n b e).hom) q :=
  normalizedRelabel_subgroup n b q e

/-- The natural modular maps commute with every base change of a normalized parameter. -/
theorem normalizedModuliMap_pullback {T U : Scheme} (b : Bool)
    (g : U ⟶ T) (q : T ⟶ normalizedLocus n b) :
    (normalizedModuliMap n b).app (Opposite.op U) (ULift.up (g ≫ q)) =
      ampleCyclicClassesPullback g n
        ((normalizedModuliMap n b).app (Opposite.op T) (ULift.up q)) := by
  exact congrArg (fun k : ULift.{1} (T ⟶ normalizedLocus n b) ⟶
    ampleCyclicClasses U n ↦ k (ULift.up q)) ((normalizedModuliMap n b).naturality g.op)

/-- Two parameters for one original object are unmarked-related on every common test. -/
theorem unmarkedRelated_overlap {S T U V : Scheme} (b c : Bool)
    (z : ampleCyclicClasses S n) (f : T ⟶ S) (g : U ⟶ S)
    (q : T ⟶ normalizedLocus n b) (r : U ⟶ normalizedLocus n c)
    (hq : (normalizedModuliMap n b).app (Opposite.op T) (ULift.up q) =
      ampleCyclicClassesPullback f n z)
    (hr : (normalizedModuliMap n c).app (Opposite.op U) (ULift.up r) =
      ampleCyclicClassesPullback g n z)
    (a : V ⟶ T) (e : V ⟶ U) (hae : a ≫ f = e ≫ g) :
    UnmarkedRelated n b c (a ≫ q) (e ≫ r) := by
  apply (unmarkedRelated_iff_moduli_eq n b c _ _).mpr
  rw [normalizedModuliMap_pullback, normalizedModuliMap_pullback, hq, hr]
  exact (congrFun (ampleCyclicClassesPullback_comp f a n) z).symm.trans
    ((congrArg (fun k ↦ ampleCyclicClassesPullback k n z) hae).trans
      (congrFun (ampleCyclicClassesPullback_comp g e n) z))

end FLT.Mazur.CyclicCharacteristicAtlas
