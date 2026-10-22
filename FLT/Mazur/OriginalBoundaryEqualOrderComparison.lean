/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryAscendingComparisonTests
public import FLT.Mazur.RelativeDoubleRankCofinalEquations
public import FLT.Mazur.RelativeDoubleRankEqualOrderLifts
public import FLT.Mazur.OriginalBoundaryDoubleRankGlobalLifts

/-!
# Full original comparison from ascending equal-order equations

Ascending ranks, including equal ranks, at equal infinitesimal orders detect
full comparison on every locally Noetherian test. Actual original arrows on
independent ranks only need equal-order tails once full comparison closedness
is available. No arrow or scalar-source finiteness is inferred from rank alone.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance equalOrderOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance equalOrderOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι

/-- Ascending ranks at equal orders detect every full independent-order endpoint equation. -/
theorem originalBoundary_endpoint_equations_iff_ascending_equal_orders (N : ℕ)
    (a : Γ(J.subscheme, ⊤)) :
    (∀ n m : Fin (N + 1), ∀ r s : ℕ,
      (doubleRankMap (Over.mk p) x y n.val m.val r s ≫ pullback.fst f f).appTop a =
        (doubleRankMap (Over.mk p) x y n.val m.val r s ≫ pullback.snd f f).appTop a) ↔
    ∀ n m : Fin (N + 1), n.val ≤ m.val → ∀ k : ℕ,
      (doubleRankMap (Over.mk p) x y n.val m.val k k ≫ pullback.fst f f).appTop a =
        (doubleRankMap (Over.mk p) x y n.val m.val k k ≫ pullback.snd f f).appTop a := by
  refine (originalBoundary_endpoint_equations_iff_ascending J N a).trans ?_
  constructor
  · exact fun h n m hnm k ↦ h n m hnm k k
  · intro h n m hnm
    exact (doubleRank_sections_iff_equal_orders (Over.mk p) x y n.val m.val
      ((pullback.fst f f).appTop a) ((pullback.snd f f).appTop a)).mpr (h n m hnm)

variable [IsNoetherian A] [QuasiCompact p]
local instance equalOrderOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

/-- A single finite ascending family at equal orders detects every full Noetherian test. -/
theorem exists_originalBoundary_equal_order_comparison_detection :
    ∃ N : ℕ, ∀ a : Γ(J.subscheme, ⊤),
      (∀ n m : Fin (N + 1), n.val ≤ m.val → ∀ k : ℕ,
        (doubleRankMap (Over.mk p) x y n.val m.val k k ≫ pullback.fst f f).appTop a =
          (doubleRankMap (Over.mk p) x y n.val m.val k k ≫ pullback.snd f f).appTop a) →
      ∀ (B : Scheme.{0}) (_ : IsLocallyNoetherian B) (b : B ⟶ pullback f f),
        (b ≫ pullback.fst f f).appTop a = (b ≫ pullback.snd f f).appTop a := by
  let hd := exists_originalBoundary_ascending_comparison_detection (p := p) (q := q) J
  let N := hd.choose
  have hN := hd.choose_spec
  refine ⟨N, fun a ha ↦ hN a ?_⟩
  exact (originalBoundary_endpoint_equations_iff_ascending J N a).mp
    ((originalBoundary_endpoint_equations_iff_ascending_equal_orders J N a).mpr ha)

variable [IsAffine A] {B : Scheme.{0}} [IsLocallyNoetherian B]
  (e : CategoryTheory.EquivalenceRelation p q) (hJ : J.comap p = J.comap q)
local notation "c" => originalBoundaryComparison p q J hJ

include e in
/-- Equal-order tails of actual original arrows construct the unique entire coefficient arrow. -/
theorem originalBoundary_global_lift_of_equal_order_tails
    (t : B ⟶ pullback f f) [IsFinite (pullback.snd p (t ≫ x))]
    (h : ∀ n m : ℕ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      ∃ d : doubleRankThickening (Over.mk p) (t ≫ x) (t ≫ y) n m k k ⟶
        pullback p J.subschemeι,
        d ≫ c = doubleRankMap (Over.mk p) (t ≫ x) (t ≫ y) n m k k ≫ t) :
    ∃! d : B ⟶ pullback p J.subschemeι, d ≫ c = t := by
  let _ := originalBoundaryComparison_mono e J hJ
  let _ := originalBoundary_comparison_test_closedImmersion J hJ t e
  exact existsUnique_global_lift_of_equal_order_tails (Over.mk p) (t ≫ x) (t ≫ y) c t h

end FLT.Mazur.EquivalenceRelationOrderedFrames
