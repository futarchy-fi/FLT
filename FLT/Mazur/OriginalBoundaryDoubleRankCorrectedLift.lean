/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankResidualCorrections
public import FLT.Mazur.OriginalBoundaryResidualCoefficientLift

/-!
# Original invariant numerators on the full off-diagonal rank rectangle

An exact residual rank equation constructs one original invariant numerator
whose boundary values agree with a powered prescribed scalar multiple of the
full invariant section on every off-diagonal chart. No power is cancelled,
and no claim of detection by the off-diagonal charts is made.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
open SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A S : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  [QuasiCompact p] [IsAffine A] (J : A.IdealSheafData)
  (e : CategoryTheory.EquivalenceRelation p q) (hJ : J.comap p = J.comap q)
  [IsAffine S] (g : A ⟶ S) (hg : p ≫ g = q ≫ g) [IsSeparated g]
  (t : compatibleFunctions (pullback.snd p J.subschemeι)
    (InvariantIdealRelation.snd J p q hJ))
local instance correctedLiftOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance correctedLiftOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
  originalBoundaryResidualDoubleRankIdeal originalBoundaryDoubleRankKernel
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))

include e hg in
/-- A shared residual rank equation constructs one original invariant lift on the full charts. -/
theorem originalBoundary_doubleRank_corrected_lift (N r s : ℕ) (a : R)
    (ha : a ∈ originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s) :
    ∃ (k : ℕ) (u : R), ∀ n m : Fin (N + 1), n.val ≠ m.val →
      (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ u) =
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop
          (σ (a ^ k) * (pullback.fst f f).appTop t.val) := by
  let hc := (mem_originalBoundaryResidualDoubleRankIdeal
    (p := p) (q := q) J N r s a).mp ha
  let b := hc.choose
  have hb := hc.choose_spec.1
  have hab := hc.choose_spec.2
  let φ (i : doubleRankOffDiagonal N) : Γ(J.subscheme, ⊤) →+*
      Γ(doubleRankThickening (Over.mk p) x y i.val.1.val i.val.2.val r s, ⊤) :=
    (doubleRankMap (Over.mk p) x y i.val.1.val i.val.2.val r s).appTop.hom.comp
      (pullback.fst f f).appTop.hom
  let hl := originalBoundary_residual_coefficient_lift (p := p) (q := q)
    J e hJ g hg t φ a
    ⟨b, hb, fun i ↦ hab i.val.1 i.val.2 i.property⟩
  let k := hl.choose
  let u := hl.choose_spec.choose
  have hu := hl.choose_spec.choose_spec
  refine ⟨k, u, fun n m hnm ↦ ?_⟩
  have hi := hu ⟨(n, m), hnm⟩
  change (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ u) =
    (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop
      ((pullback.fst f f).appTop (algebraMap R Γ(J.subscheme, ⊤) (a ^ k) * t.val)) at hi
  exact hi.trans (congrArg (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop
    (map_mul (pullback.fst f f).appTop.hom _ _))

include e hg in
/-- An exact ideal power gives original numerators for every scalar in the whole target ideal. -/
theorem originalBoundary_doubleRank_corrected_lift_of_power (N r s : ℕ) (Q : Ideal R)
    (d : ℕ) (hd : Q ^ d ≤
      originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N r s)
    (a : R) (ha : a ∈ Q) :
    ∃ (k : ℕ) (u : R), ∀ n m : Fin (N + 1), n.val ≠ m.val →
      (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ u) =
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop
          (σ (a ^ (d * k)) * (pullback.fst f f).appTop t.val) := by
  let hl := originalBoundary_doubleRank_corrected_lift (p := p) (q := q)
    J e hJ g hg t N r s
    (a ^ d) (hd (Ideal.pow_mem_pow ha d))
  let k := hl.choose
  let u := hl.choose_spec.choose
  have hu := hl.choose_spec.choose_spec
  exact ⟨k, u, fun n m hnm ↦ by simpa only [pow_mul] using hu n m hnm⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
