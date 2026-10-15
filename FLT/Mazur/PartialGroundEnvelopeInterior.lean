/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PartialCompactTranslationInterior
public import FLT.Mazur.PartialTranslationNormSupport

/-!
# Original full interiors from partial charts after independent ground change

Only the ambient translation is Cartesian. Partial finite charts cover the
excluded changed-envelope points. Fullness then descends through the actual
Cartesian square, and openness through the open surjective source map.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace FLT.Mazur.SchemeTranslationNorm
open Approximation SchemeOpenEnvelope HilbertChart.AffineRestriction
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
variable {R S : Type} [CommRing R] [CommRing S]
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (w : (Over.map a).obj W ⟶ V) (H : IsPullback w.left W.hom V.hom a)
  {A : Over (Spec (.of R))} {B : Over (Spec (.of S))}
  (u : (Over.map a).obj B ⟶ A)
  {I : Type} [Finite I] (T : I → Over (Spec (.of S))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- Norms and proper projections use the individual partial-chart algebras. -/
local instance partialGroundTranslationAlgebra (i : I) : Algebra S Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) S Γ((T i).left, ⊤))
  (U : (prod A V).left.Opens)
  (ht : ∀ y : (prod B W).left, (fixedBaseEnvelopeMap a V W w u).left y ∉ U →
    ∃ i, ∃ z : (T i).left, (t i).left z = (prod.snd : prod B W ⟶ W).left y)
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "e" => Over.Hom.left (fixedBaseEnvelopeMap a V W w u)

include H b ht

/-- Partial finite charts make the inverse image of the ORIGINAL full-fiber locus open. -/
theorem isOpen_preimage_originalFullFiber_of_partialGroundCover :
    IsOpen (u.left ⁻¹' fullFiberLocus π U) := by
  exact (congrArg IsOpen (fullFiberLocus_baseChange
    (fixedBaseEnvelopeMap_isPullback a V W w u H) U)).mp
      (isOpen_fullFiber_open_of_partialFiniteTranslation B W T t b (e ⁻¹ᵁ U) ht)

/-- Open surjective source descent constructs the original open for arbitrary envelope opens. -/
theorem isOpen_originalFullFiber_of_partialGroundCover
    (hu : IsOpenMap u.left) (hsurj : Function.Surjective u.left) :
    IsOpen (fullFiberLocus π U) :=
  (hu.isQuotientMap u.left.continuous hsurj).isCoinducing.isOpen_preimage.mp
    (isOpen_preimage_originalFullFiber_of_partialGroundCover a V W w H u T t b U ht)

/-- No original full fiber is lost on passing to the actual maximal open. -/
theorem originalFullInterior_eq_of_partialGroundCover
    (hu : IsOpenMap u.left) (hsurj : Function.Surjective u.left) :
    (fullFiberInterior π U : Set A.left) = fullFiberLocus π U :=
  (isOpen_originalFullFiber_of_partialGroundCover a V W w H u T t b U ht hu hsurj).interior_eq

omit [Finite I] in
/-- An arbitrary open family of partial charts suffices when the changed envelope is affine. -/
theorem isOpen_originalFullFiber_of_affinePartialGroundCover
    [IsAffine B.left] [IsAffine W.left]
    (ho : ∀ i, IsOpen (Set.range (t i).left))
    (hu : IsOpenMap u.left) (hsurj : Function.Surjective u.left) :
    IsOpen (fullFiberLocus π U) := by
  apply (hu.isQuotientMap u.left.continuous hsurj).isCoinducing.isOpen_preimage.mp
  exact (congrArg IsOpen (fullFiberLocus_baseChange
    (fixedBaseEnvelopeMap_isPullback a V W w u H) U)).mp
      (isOpen_fullFiber_open_of_affine_partialTranslation B W T t (e ⁻¹ᵁ U) ht ho b)

/-- The actual original source has denominators retaining every point of a given finite set. -/
theorem exists_originalDenominator_of_partialGroundCover [IsAffine A.left]
    (hu : IsOpenMap u.left) (hsurj : Function.Surjective u.left)
    (F : Set A.left) (hF : F.Finite) (hFU : F ⊆ fullFiberLocus π U) :
    ∃ r : Γ(A.left, ⊤), F ⊆ A.left.basicOpen r ∧ r ∈ denominatorIdeal (π).appTop.hom U := by
  apply exists_fullFiberInterior_coefficient π U F hF
  rwa [originalFullInterior_eq_of_partialGroundCover a V W w H u T t b U ht hu hsurj]

omit U ht [Finite I] in
/-- For a principal open the actual finite norm product still computes the original full fiber. -/
theorem basicOpen_partialGroundNorm_fullFiber [Fintype I]
    (s : Γ((prod A V).left, ⊤))
    (ht : ∀ y : (prod B W).left, (e) y ∉ (prod A V).left.basicOpen s →
      ∃ i, ∃ z : (T i).left, (t i).left z = (prod.snd : prod B W ⟶ W).left y) :
    (B.left.basicOpen (jointTranslationNorm B W T t b ((e).appTop s)) : Set B.left) =
      u.left ⁻¹' fullFiberLocus π ((prod A V).left.basicOpen s) := by
  refine Eq.trans ?_
    (fullFiberLocus_baseChange (fixedBaseEnvelopeMap_isPullback a V W w u H) _)
  rw [Scheme.preimage_basicOpen_top]
  apply basicOpen_partialTranslationNorm_fullFiber B W T t b _
  intro y hy
  apply ht y
  change y ∉ (e) ⁻¹ᵁ (prod A V).left.basicOpen s
  rwa [Scheme.preimage_basicOpen_top]

end FLT.Mazur.SchemeTranslationNorm
