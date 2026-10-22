/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryBoundedOrderCorrections
public import FLT.Mazur.OriginalBoundaryDoubleRankCorrectedLift

/-!
# One original invariant numerator across bounded rank orders

An exact residual scalar at a common upper order constructs one original
invariant numerator. That same numerator gives the required powered boundary
value on every lower independent order. Ascending support inputs produce such
numerators for every scalar in the whole finitely generated target ideal.
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
local instance boundedNumeratorOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance boundedNumeratorOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))
local notation "H" => originalBoundaryResidualIdeal (p := p) (q := q) J

include e hg in
/-- One original invariant numerator solves every smaller full off-diagonal rank order. -/
theorem originalBoundary_bounded_order_numerator (N k : ℕ) (a : R)
    (ha : a ∈ originalBoundaryResidualDoubleRankIdeal (p := p) (q := q) J N k k) :
    ∃ (d : ℕ) (u : R), ∀ r s : ℕ, r ≤ k → s ≤ k →
      ∀ n m : Fin (N + 1), n.val ≠ m.val →
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ u) =
          (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop
            (σ (a ^ d) * (pullback.fst f f).appTop t.val) := by
  let hl := originalBoundary_doubleRank_corrected_lift J e hJ g hg t N k k a ha
  let d := hl.choose
  let u := hl.choose_spec.choose
  have hu := hl.choose_spec.choose_spec
  exact ⟨d, u, fun r s hr hs n m hnm ↦
    doubleRankTransition_section_eq (Over.mk p) x y n.val m.val hr hs _ _ (hu n m hnm)⟩

variable [TopologicalSpace.NoetherianSpace A]

include e hg in
/-- Ascending geometric support data constructs full original numerators on every bounded box. -/
theorem originalBoundary_ascending_bounded_order_numerators
    (N r₀ s₀ : ℕ) (Q : Ideal R) (hfg : Q.FG)
    (h : ∀ n m : Fin (N + 1), n.val < m.val →
      Q ≤ (doubleRankScalarKernel (Over.mk p) x y σ n.val m.val r₀ s₀ ⊔ H).radical)
    (k : ℕ) (a : R) (ha : a ∈ Q) :
    ∃ (d : ℕ) (u : R), ∀ r s : ℕ, r ≤ k → s ≤ k →
      ∀ n m : Fin (N + 1), n.val ≠ m.val →
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop (σ u) =
          (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop
            (σ (a ^ d) * (pullback.fst f f).appTop t.val) := by
  let hp := originalBoundary_ascending_residual_powers_all_orders J N r₀ s₀ Q hfg h k k
  let b := hp.choose
  have hb := hp.choose_spec
  let hl := originalBoundary_bounded_order_numerator J e hJ g hg t N k
    (a ^ b) (hb (Ideal.pow_mem_pow ha b))
  let d := hl.choose
  let u := hl.choose_spec.choose
  have hu := hl.choose_spec.choose_spec
  exact ⟨b * d, u, fun r s hr hs n m hnm ↦ by
    simpa only [pow_mul] using hu r s hr hs n m hnm⟩

end FLT.Mazur.EquivalenceRelationOrderedFrames
