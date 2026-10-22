/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.OriginalBoundaryDoubleRankTests
public import FLT.Mazur.OriginalBoundaryComparisonNeighborhood

/-!
# Full original coefficients without finiteness of the unsplit test

Original arrows on all independent rank thickenings detect both comparison
kernel equations and every full invariant boundary value. The coefficient
test only needs to be locally Noetherian. Finiteness of the source over that
unsplit test, needed for the closed-comparison arrow construction, is not
needed for these full coefficient equations.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.EquivalenceRelationOrderedFrames
open RelativeOrderedTuples RingPairInvariantFlatScalars SchemeScalarPrincipalNeighborhood
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
private theorem kernel_le_of_rank_lifts {S B C Y : Scheme.{0}} [IsNoetherian S]
    (E : Over S) [Etale E.hom] [IsSeparated E.hom] [QuasiCompact E.hom]
    [IsLocallyNoetherian B] (x y : B ⟶ S) (c : C ⟶ Y) (t : B ⟶ Y)
    (h : ∀ n m r s : ℕ, ∃ d : doubleRankThickening E x y n m r s ⟶ C,
      d ≫ c = doubleRankMap E x y n m r s ≫ t) :
    RingHom.ker c.appTop.hom ≤ RingHom.ker t.appTop.hom := by
  intro a ha
  change t.appTop a = 0
  apply (section_eq_iff_doubleRank_stages E x y _ _).mpr
  intro n m r s
  obtain ⟨d, hd⟩ := h n m r s
  rw [map_zero]
  change ((t.appTop) ≫ (doubleRankMap E x y n m r s).appTop) a = 0
  rw [← Scheme.Hom.comp_appTop, ← hd, Scheme.Hom.comp_appTop]
  change d.appTop (c.appTop a) = 0
  rw [show c.appTop a = 0 from ha, map_zero]

variable {D A B : Scheme.{0}} {p q : D ⟶ A}
  [IsNoetherian A] [IsSeparated p] [Etale p] [QuasiCompact p]
  [IsLocallyNoetherian B] (J : A.IdealSheafData) (hJ : J.comap p = J.comap q)
local instance doubleCoefficientOver_separated : IsSeparated (Over.mk p).hom := ‹IsSeparated p›
local instance doubleCoefficientOver_etale : Etale (Over.mk p).hom := ‹Etale p›
local instance doubleCoefficientOver_compact : QuasiCompact (Over.mk p).hom := ‹QuasiCompact p›
attribute [local instance] sourceAlgebra targetAlgebra originalBoundaryAlgebra
set_option quotPrecheck false
local notation "R" => invariants p.appTop.hom q.appTop.hom
local notation "f" => scalarMorphism (algebraMap R Γ(J.subscheme, ⊤))
local notation "x" => pullback.fst f f ≫ J.subschemeι
local notation "y" => pullback.snd f f ≫ J.subschemeι
local notation "c" => originalBoundaryComparison p q J hJ

/-- Every original comparison equation vanishes on the entire unsplit coefficient test. -/
theorem originalBoundary_kernel_le_of_doubleRank_arrows
    (t : B ⟶ pullback f f)
    (h : ∀ n m r s : ℕ,
      ∃ d : doubleRankThickening (Over.mk p) (t ≫ x) (t ≫ y) n m r s ⟶
        pullback p J.subschemeι,
      d ≫ c = doubleRankMap (Over.mk p) (t ≫ x) (t ≫ y) n m r s ≫ t) :
    RingHom.ker (c).appTop.hom ≤ RingHom.ker t.appTop.hom := by
  exact kernel_le_of_rank_lifts (Over.mk p) (t ≫ x) (t ≫ y) c t h

/-- Full invariant agreement follows without assuming finiteness over the original scalars. -/
theorem originalBoundary_invariant_eq_of_doubleRank_arrows
    (t : B ⟶ pullback f f)
    (h : ∀ n m r s : ℕ,
      ∃ d : doubleRankThickening (Over.mk p) (t ≫ x) (t ≫ y) n m r s ⟶
        pullback p J.subschemeι,
      d ≫ c = doubleRankMap (Over.mk p) (t ≫ x) (t ≫ y) n m r s ≫ t)
    (a : SchemeEffectiveEpiSections.compatibleFunctions
      (pullback.snd p J.subschemeι) (InvariantIdealRelation.snd J p q hJ)) :
    (t ≫ pullback.fst f f).appTop a.val = (t ≫ pullback.snd f f).appTop a.val := by
  have hk : (pullback.fst f f).appTop a.val - (pullback.snd f f).appTop a.val ∈
      RingHom.ker (c).appTop.hom := by
    change (c).appTop (_ - _) = 0
    rw [map_sub]
    apply sub_eq_zero.mpr
    change ((pullback.fst f f).appTop ≫ (c).appTop) a.val =
      ((pullback.snd f f).appTop ≫ (c).appTop) a.val
    rw [← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop]
    have ha : (pullback.snd p J.subschemeι).appTop a.val =
        (InvariantIdealRelation.snd J p q hJ).appTop a.val := a.property
    simpa only [originalBoundaryComparison, pullback.lift_fst, pullback.lift_snd] using ha
  have hz := originalBoundary_kernel_le_of_doubleRank_arrows J hJ t h hk
  change t.appTop (_ - _) = 0 at hz
  rw [map_sub, sub_eq_zero] at hz
  simpa only [Scheme.Hom.comp_appTop, ConcreteCategory.comp_apply] using hz

end FLT.Mazur.EquivalenceRelationOrderedFrames
