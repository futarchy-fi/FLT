/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryCompleteRankKernel
public import FLT.Mazur.RelativeDoubleRankBoundedDetection

/-!
# Exact original boundary detection by the complete rank tower

One finite rectangle at all independent orders detects full boundary sections,
not just their reductions. Consequently the intersection of its exact scalar
kernels is the original boundary scalar kernel itself. No interchange of an
infinite intersection with a residual ideal sum is asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem section_retraction {X Y : Scheme.{0}} (l : Y ⟶ X) (d : X ⟶ Y)
    (hd : d ≫ l = 𝟙 X) (a : Γ(X, ⊤)) : d.appTop (l.appTop a) = a := by
  change (l.appTop ≫ d.appTop) a = a
  rw [← Scheme.Hom.comp_appTop, hd, Scheme.Hom.id_appTop]
  rfl

private theorem retraction_rank_detection {S X Y : Scheme.{0}} [IsNoetherian S]
    [IsLocallyNoetherian X] (E : Over S) [Etale E.hom] [IsSeparated E.hom]
    [QuasiCompact E.hom] (x y : Y ⟶ S) (l : Y ⟶ X) (d : X ⟶ Y)
    (hd : d ≫ l = 𝟙 X) :
    ∃ N : ℕ, ∀ a b : Γ(X, ⊤),
      (∀ n m : Fin (N + 1), ∀ r s : ℕ,
        (doubleRankMap E x y n.val m.val r s).appTop (l.appTop a) =
          (doubleRankMap E x y n.val m.val r s).appTop (l.appTop b)) ↔ a = b := by
  obtain ⟨N, hN⟩ := exists_bounded_doubleRank_test_detection E x y
  refine ⟨N, fun a b ↦ ⟨fun h ↦ ?_, fun h _ _ _ _ ↦ congrArg _ (congrArg _ h)⟩⟩
  have he := hN X inferInstance d (l.appTop a) (l.appTop b) h
  exact (section_retraction l d hd a).symm.trans (he.trans (section_retraction l d hd b))

private theorem retraction_rank_kernel {S X Y : Scheme.{0}} [IsNoetherian S]
    [IsLocallyNoetherian X] (E : Over S) [Etale E.hom] [IsSeparated E.hom]
    [QuasiCompact E.hom] (x y : Y ⟶ S) (l : Y ⟶ X) (d : X ⟶ Y)
    (hd : d ≫ l = 𝟙 X) {R : Type} [CommRing R] (σ : R →+* Γ(X, ⊤)) :
    ∃ N : ℕ, (⨅ r : ℕ, ⨅ s : ℕ,
      doubleRankCompleteKernel E x y (l.appTop.hom.comp σ) N r s) = RingHom.ker σ := by
  obtain ⟨N, hN⟩ := retraction_rank_detection E x y l d hd
  refine ⟨N, ?_⟩
  ext a
  constructor
  · intro ha
    apply (hN (σ a) 0).mp
    intro n m r s
    have hi := (mem_doubleRankCompleteKernel E x y (l.appTop.hom.comp σ) N r s a).mp
      (Ideal.mem_iInf.mp (Ideal.mem_iInf.mp ha r) s) n m
    simpa only [RingHom.comp_apply, map_zero] using hi
  · intro ha
    apply Ideal.mem_iInf.mpr
    intro r
    apply Ideal.mem_iInf.mpr
    intro s
    apply (mem_doubleRankCompleteKernel E x y (l.appTop.hom.comp σ) N r s a).mpr
    intro n m
    change (doubleRankMap E x y n.val m.val r s).appTop (l.appTop (σ a)) = 0
    rw [show σ a = 0 from ha, map_zero, map_zero]

variable {D A : Scheme.{0}} {p q : D ⟶ A} [IsNoetherian A]
  [IsSeparated p] [Etale p] [QuasiCompact p] (J : A.IdealSheafData)
local instance completeDetectOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance completeDetectOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance completeDetectOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
local instance completeDetectBoundary_noetherian : IsLocallyNoetherian J.subscheme :=
  LocallyOfFiniteType.isLocallyNoetherian J.subschemeι
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
attribute [local irreducible] doubleRankMap doubleRankThickening
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "σ" => (pullback.fst f f).appTop.hom.comp (algebraMap R Γ(J.subscheme, ⊤))

/-- All orders of one finite complete rectangle detect actual original boundary coefficients. -/
theorem exists_originalBoundary_complete_rank_section_detection :
    ∃ N : ℕ, ∀ a b : Γ(J.subscheme, ⊤),
      (∀ n m : Fin (N + 1), ∀ r s : ℕ,
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop
          ((pullback.fst f f).appTop a) =
        (doubleRankMap (Over.mk p) x y n.val m.val r s).appTop
          ((pullback.fst f f).appTop b)) ↔ a = b := by
  exact retraction_rank_detection (Over.mk p) x y (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f)

/-- The full nonreduced original scalar kernel is exactly the complete all-order intersection. -/
theorem exists_originalBoundary_complete_rank_kernel_intersection :
    ∃ N : ℕ, (⨅ r : ℕ, ⨅ s : ℕ,
      originalBoundaryCompleteRankKernel (p := p) (q := q) J N r s) =
        originalBoundaryScalarKernel (p := p) (q := q) J := by
  exact retraction_rank_kernel (Over.mk p) x y (pullback.fst f f)
    (pullback.diagonal f) (pullback.diagonal_fst f) (algebraMap R Γ(J.subscheme, ⊤))

end FLT.Mazur.EquivalenceRelationOrderedFrames
