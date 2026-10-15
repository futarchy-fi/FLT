/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PartialGroundEnvelopeInterior
public import FLT.Mazur.AffineHilbertFullInteriorChart

/-!
# Original Hilbert full interiors from partial ground charts

The finite charts only cover the missing original relation after independent
base change. Under this explicit coverage condition, every original full fiber
lies in the actual full-interior chart. Whole scheme tests lift uniquely.
No affineness of the original source or translation is needed.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeTranslationNorm
open SchemeEffectiveEpiSections
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd toEnvelope
variable {R S : Type} [CommRing R] [CommRing S] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  (w : (Over.map a).obj W ⟶ V) (H : IsPullback w.left W.hom V.hom a)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left] {B : Over (Spec (.of S))}
  (u : (Over.map a).obj B ⟶ A) (hu : IsOpenMap u.left)
  (hsurj : Function.Surjective u.left)
  {I : Type} [Finite I] (T : I → Over (Spec (.of S))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- Finite bases are needed only for the partial translation charts. -/
local instance hilbertPartialGroundTranslationAlgebra (i : I) : Algebra S Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) S Γ((T i).left, ⊤))
  (ht : ∀ y : (prod B W).left,
    (fixedBaseEnvelopeMap a V W w u).left y ∉ (toEnvelope f hL d V c k).left.opensRange →
      ∃ i, ∃ z : (T i).left, (t i).left z = (prod.snd : prod B W ⟶ W).left y)
local notation "U" => fullEnvelopeInterior f hL d V c k
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)

include H hu hsurj b ht

/-- Partial coverage of missing relation points proves openness of the ORIGINAL full-fiber locus. -/
theorem fullEnvelopeLocus_isOpen_of_partialGroundCover :
    IsOpen (fullEnvelopeLocus f hL d V c k) :=
  isOpen_originalFullFiber_of_partialGroundCover a V W w H u T t b (j).opensRange ht hu hsurj

omit [Finite I] in
/-- Affine changed envelopes allow arbitrary open partial families by finite extraction. -/
theorem fullEnvelopeLocus_isOpen_of_affinePartialGroundCover
    [IsAffine B.left] [IsAffine W.left]
    (ho : ∀ i, IsOpen (Set.range (t i).left)) :
    IsOpen (fullEnvelopeLocus f hL d V c k) :=
  isOpen_originalFullFiber_of_affinePartialGroundCover
    a V W w H u T t b (j).opensRange ht ho hu hsurj

/-- Every full original independent fiber survives in the actual source open. -/
theorem fullEnvelopeInterior_eq_locus_of_partialGroundCover :
    (U : Set A.left) = fullEnvelopeLocus f hL d V c k :=
  (fullEnvelopeLocus_isOpen_of_partialGroundCover
    f hL d a V W w H c k u hu hsurj T t b ht).interior_eq

/-- The chart's range is exactly the original full-fiber locus, not a changed-family locus. -/
theorem fullInteriorSourceMap_range_of_partialGroundCover :
    Set.range (fullInteriorSourceMap f hL d V c k).left = fullEnvelopeLocus f hL d V c k := by
  change Set.range (U).ι = _
  rw [Scheme.Opens.range_ι]
  exact fullEnvelopeInterior_eq_locus_of_partialGroundCover
    f hL d a V W w H c k u hu hsurj T t b ht

/-- Every retained original point has a preimage on the actual full-envelope chart. -/
theorem exists_fullInterior_preimage_of_partialGroundCover (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) :
    ∃ y : (fullInteriorSource f hL d V c k).left,
      (fullInteriorSourceMap f hL d V c k).left y = x := by
  change x ∈ Set.range (fullInteriorSourceMap f hL d V c k).left
  rwa [fullInteriorSourceMap_range_of_partialGroundCover
    f hL d a V W w H c k u hu hsurj T t b ht]

/-- The retained point has an actual admissible invariant coefficient on the constructed chart. -/
theorem exists_invariant_coefficient_of_partialGroundCover [Etale V.hom] (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) :
    ∃ y : (fullInteriorSource f hL d V c k).left,
      ∃ r : compatibleFunctions
        (fst f hL d V c (fullInteriorChart f hL d V c k)).left
        (snd f hL d V c (fullInteriorChart f hL d V c k)).left,
        (fullInteriorSourceMap f hL d V c k).left y = x ∧
          r ∈ invariantEnvelopeDenominators f hL d V c (fullInteriorChart f hL d V c k) ∧
            y ∈ (fullInteriorSource f hL d V c k).left.basicOpen r.val := by
  obtain ⟨y, hy⟩ := exists_fullInterior_preimage_of_partialGroundCover
    f hL d a V W w H c k u hu hsurj T t b ht x hx
  obtain ⟨r, hr, hyr⟩ := fullInteriorChart_nonvanishing f hL d V c k y
  exact ⟨y, r, hy, hr, hyr⟩

variable {Z : Scheme} (g : Z ⟶ A.left)
  (hg : Set.range g ⊆ fullEnvelopeLocus f hL d V c k)

/-- Lift the complete scheme test into the actual original full-envelope chart. -/
def partialGroundFullInteriorLift : Z ⟶ (fullInteriorSource f hL d V c k).left := by
  change Z ⟶ (U).toScheme
  exact IsOpenImmersion.lift (U).ι g (by
    rw [Scheme.Opens.range_ι, fullEnvelopeInterior_eq_locus_of_partialGroundCover
      f hL d a V W w H c k u hu hsurj T t b ht]
    exact hg)

/-- The full source map, including its coefficient and nilpotent information, is retained. -/
@[reassoc]
theorem partialGroundFullInteriorLift_comp :
    partialGroundFullInteriorLift f hL d a V W w H c k u hu hsurj T t b ht g hg ≫
      (fullInteriorSourceMap f hL d V c k).left = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The whole lifted morphism is uniquely determined by the original test morphism. -/
theorem partialGroundFullInteriorLift_unique
    (l : Z ⟶ (fullInteriorSource f hL d V c k).left)
    (hl : l ≫ (fullInteriorSourceMap f hL d V c k).left = g) :
    l = partialGroundFullInteriorLift f hL d a V W w H c k u hu hsurj T t b ht g hg := by
  apply (cancel_mono (U).ι).mp
  exact hl.trans
    (partialGroundFullInteriorLift_comp f hL d a V W w H c k u hu hsurj T t b ht g hg).symm

end FLT.Mazur.HilbertChart.AffineRestriction
