/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryRankEndpointTransposition
public import FLT.Mazur.RelativeDoubleRankBoundedDetection

/-!
# Ascending full comparison equations on original coefficient tests

Both endpoints agree on every full chart exactly when they agree on the
ascending charts at all independent orders. Equal-rank charts remain required.
One finite such family detects the comparison equation on every locally
Noetherian coefficient test, without assuming the original scalar pair finite.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem swapped_equations_iff {R S : Type} [CommRing R] [CommRing S]
    (f : S →+* R) (g : R →+* S) (a b : R) (c d : S)
    (hf₁ : f c = b) (hf₂ : f d = a) (hg₁ : g a = d) (hg₂ : g b = c) :
    a = b ↔ c = d := by
  exact ⟨fun h ↦ hg₂.symm.trans ((congrArg g h).symm.trans hg₁),
    fun h ↦ hf₂.symm.trans ((congrArg f h).symm.trans hf₁)⟩

private theorem symmetric_rows_iff_ascending (P : ℕ → ℕ → ℕ → ℕ → Prop)
    (hP : ∀ n m r s, P n m r s ↔ P m n s r) (N : ℕ) :
    (∀ n m : Fin (N + 1), ∀ r s : ℕ, P n.val m.val r s) ↔
      ∀ n m : Fin (N + 1), n.val ≤ m.val → ∀ r s : ℕ, P n.val m.val r s := by
  constructor
  · exact fun h n m _ ↦ h n m
  · intro h n m r s
    by_cases hnm : n.val ≤ m.val
    · exact h n m hnm r s
    · exact (hP n.val m.val r s).mpr
        (h m n (Nat.le_of_lt (Nat.lt_of_not_ge hnm)) s r)

private theorem ascending_test_detection {S X B : Scheme.{0}} [IsNoetherian S]
    (E : Over S) [Etale E.hom] [IsSeparated E.hom] [QuasiCompact E.hom]
    (x y : B ⟶ S) (l h : B ⟶ X)
    (hs : ∀ (a : Γ(X, ⊤)) (n m r s : ℕ),
      (doubleRankMap E x y n m r s ≫ l).appTop a =
        (doubleRankMap E x y n m r s ≫ h).appTop a ↔
      (doubleRankMap E x y m n s r ≫ l).appTop a =
        (doubleRankMap E x y m n s r ≫ h).appTop a) :
    ∃ N : ℕ, ∀ a : Γ(X, ⊤),
      (∀ n m : Fin (N + 1), n.val ≤ m.val → ∀ r s : ℕ,
        (doubleRankMap E x y n.val m.val r s ≫ l).appTop a =
          (doubleRankMap E x y n.val m.val r s ≫ h).appTop a) →
      ∀ (T : Scheme.{0}) (_ : IsLocallyNoetherian T) (v : T ⟶ B),
        (v ≫ l).appTop a = (v ≫ h).appTop a := by
  obtain ⟨N, hN⟩ := exists_bounded_doubleRank_test_detection E x y
  refine ⟨N, fun a ha T hT v ↦ ?_⟩
  exact hN T hT v (l.appTop a) (h.appTop a)
    ((symmetric_rows_iff_ascending _ (hs a) N).mpr ha)

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsSeparated p] [Etale p]
  (J : A.IdealSheafData)
local instance ascendingTestOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance ascendingTestOver_etale : Etale (Over.mk p).hom := ‹Etale p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι

/-- Full endpoint agreement transfers exactly to the transposed chart. -/
theorem originalBoundary_rank_endpoint_eq_transpose (n m r s : ℕ)
    (a : Γ(J.subscheme, ⊤)) :
    (doubleRankMap (Over.mk p) x y n m r s ≫ pullback.fst f f).appTop a =
        (doubleRankMap (Over.mk p) x y n m r s ≫ pullback.snd f f).appTop a ↔
      (doubleRankMap (Over.mk p) x y m n s r ≫ pullback.fst f f).appTop a =
        (doubleRankMap (Over.mk p) x y m n s r ≫ pullback.snd f f).appTop a := by
  exact swapped_equations_iff _ _ _ _ _ _
    (originalBoundary_rank_transpose_first_section J n m r s a)
    (originalBoundary_rank_transpose_second_section J n m r s a)
    (originalBoundary_rank_transpose_first_section J m n s r a)
    (originalBoundary_rank_transpose_second_section J m n s r a)

/-- Ascending ranks suffice for the full all-order comparison equation; the diagonal is kept. -/
theorem originalBoundary_endpoint_equations_iff_ascending (N : ℕ)
    (a : Γ(J.subscheme, ⊤)) :
    (∀ n m : Fin (N + 1), ∀ r s : ℕ,
      (doubleRankMap (Over.mk p) x y n.val m.val r s ≫ pullback.fst f f).appTop a =
        (doubleRankMap (Over.mk p) x y n.val m.val r s ≫ pullback.snd f f).appTop a) ↔
      ∀ n m : Fin (N + 1), n.val ≤ m.val → ∀ r s : ℕ,
        (doubleRankMap (Over.mk p) x y n.val m.val r s ≫ pullback.fst f f).appTop a =
          (doubleRankMap (Over.mk p) x y n.val m.val r s ≫ pullback.snd f f).appTop a := by
  exact symmetric_rows_iff_ascending _
    (fun n m r s ↦ originalBoundary_rank_endpoint_eq_transpose J n m r s a) N

variable [IsNoetherian A] [QuasiCompact p]
local instance ascendingTestOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›

/-- One finite ascending all-order family detects full comparison on every Noetherian test. -/
theorem exists_originalBoundary_ascending_comparison_detection :
    ∃ N : ℕ, ∀ a : Γ(J.subscheme, ⊤),
      (∀ n m : Fin (N + 1), n.val ≤ m.val → ∀ r s : ℕ,
        (doubleRankMap (Over.mk p) x y n.val m.val r s ≫ pullback.fst f f).appTop a =
          (doubleRankMap (Over.mk p) x y n.val m.val r s ≫ pullback.snd f f).appTop a) →
      ∀ (B : Scheme.{0}) (_ : IsLocallyNoetherian B) (b : B ⟶ pullback f f),
        (b ≫ pullback.fst f f).appTop a = (b ≫ pullback.snd f f).appTop a := by
  exact ascending_test_detection (Over.mk p) x y (pullback.fst f f) (pullback.snd f f)
    (fun a n m r s ↦ originalBoundary_rank_endpoint_eq_transpose J n m r s a)

end FLT.Mazur.EquivalenceRelationOrderedFrames
