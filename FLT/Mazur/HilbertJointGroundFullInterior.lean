/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.JointGroundEnvelopeNeighborhood
public import FLT.Mazur.AffineHilbertFullInteriorChart

/-!
# Original Hilbert full interiors detected by finite ground subcharts

A finite free joint cover of the whole changed translation proves that every
original full-envelope fiber is in the original full interior. Whole scheme
tests then factor through the actual full-envelope chart, retaining nilpotents.
Existence of the joint covers and of original full fibers is still separate.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeTranslationNorm
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd toEnvelope
variable {R S : Type} [CommRing R] [CommRing S] [Algebra.FiniteType ℤ R]
  {X : Scheme} (f : X ⟶ Spec (.of R))
  [IsProper f] [Flat f] [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L) (d : ℕ)
  (a : Spec (.of S) ⟶ Spec (.of R))
  (V : Over (Spec (.of R))) (W : Over (Spec (.of S)))
  [IsAffine V.left] [Etale V.hom]
  (w : (Over.map a).obj W ⟶ V) (H : IsPullback w.left W.hom V.hom a)
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left] {B : Over (Spec (.of S))}
  (u : (Over.map a).obj B ⟶ A) (hu : IsOpenMap u.left)
  (hsurj : Function.Surjective u.left)
  {I : Type} [Finite I] (T : I → Over (Spec (.of S))) (t : ∀ i, T i ⟶ W)
  [∀ i, IsAffine (T i).left]
/-- The finite norms only require bases on the changed-ground subcharts. -/
local instance hilbertJointGroundTranslationAlgebra (i : I) : Algebra S Γ((T i).left, ⊤) :=
  affineBaseSectionAlgebra (T i).hom
variable {ι : I → Type} [∀ i, Finite (ι i)]
  (b : ∀ i, Module.Basis (ι i) S Γ((T i).left, ⊤))
  (ht : ∀ z : W.left, ∃ i, ∃ y : (T i).left, (t i).left y = z)
local notation "U" => fullEnvelopeInterior f hL d V c k
local notation "j" => Over.Hom.left (toEnvelope f hL d V c k)

include H hu hsurj b ht

/-- Joint finite subcharts prove openness of the original full-envelope locus. -/
theorem fullEnvelopeLocus_isOpen_of_jointGroundCover :
    IsOpen (fullEnvelopeLocus f hL d V c k) :=
  isOpen_originalFullFiber_open_of_jointGroundCover a V W w H u hu hsurj T t b ht (j).opensRange

/-- Every actual original full fiber survives in the maximal original open. -/
theorem fullEnvelopeInterior_eq_locus_of_jointGroundCover :
    (U : Set A.left) = fullEnvelopeLocus f hL d V c k :=
  (fullEnvelopeLocus_isOpen_of_jointGroundCover
    f hL d a V W w H c k u hu hsurj T t b ht).interior_eq

/-- Original point counts detect membership in the constructed open, not merely in a set. -/
theorem fullEnvelopeInterior_iff_fiber_ncard_eq_of_jointGroundCover (x : A.left) :
    x ∈ U ↔
      ((snd f hL d V c k).left ⁻¹' {x}).ncard =
        ((prod.fst : prod A V ⟶ A).left ⁻¹' {x}).ncard := by
  change x ∈ (U : Set A.left) ↔ _
  rw [fullEnvelopeInterior_eq_locus_of_jointGroundCover
    f hL d a V W w H c k u hu hsurj T t b ht]
  exact fullEnvelopeLocus_iff_fiber_ncard_eq f hL d V c k x

/-- Actual distinct original arrows supply open neighborhoods from an independent fiber bound. -/
theorem fullEnvelopeInterior_of_jointGround_fiber_witnesses (x : A.left) {n : ℕ}
    (e : Fin n → (relation f hL d V c k).left) (he : Function.Injective e)
    (hq : ∀ i, (snd f hL d V c k).left (e i) = x)
    (hn : ((prod.fst : prod A V ⟶ A).left ⁻¹' {x}).ncard ≤ n) : x ∈ U := by
  change x ∈ (U : Set A.left)
  rw [fullEnvelopeInterior_eq_locus_of_jointGroundCover
    f hL d a V W w H c k u hu hsurj T t b ht]
  exact fullEnvelopeLocus_of_fiber_witnesses f hL d V c k x e he hq hn

/-- The constructed full-envelope chart covers every retained original point. -/
theorem fullInteriorSourceMap_range_of_jointGroundCover :
    Set.range (fullInteriorSourceMap f hL d V c k).left = fullEnvelopeLocus f hL d V c k := by
  change Set.range (U).ι = _
  rw [Scheme.Opens.range_ι]
  exact fullEnvelopeInterior_eq_locus_of_jointGroundCover f hL d a V W w H c k u hu hsurj T t b ht

variable {Z : Scheme} (g : Z ⟶ A.left)
  (hg : Set.range g ⊆ fullEnvelopeLocus f hL d V c k)

/-- Lift the entire scheme test, not merely its points, into the original full-envelope chart. -/
def jointGroundFullInteriorLift : Z ⟶ (fullInteriorSource f hL d V c k).left := by
  change Z ⟶ (U).toScheme
  exact IsOpenImmersion.lift (U).ι g (by
    rw [Scheme.Opens.range_ι,
      fullEnvelopeInterior_eq_locus_of_jointGroundCover f hL d a V W w H c k u hu hsurj T t b ht]
    exact hg)

/-- The lifted chart retains the complete original test morphism and its coefficient maps. -/
@[reassoc]
theorem jointGroundFullInteriorLift_comp :
    jointGroundFullInteriorLift f hL d a V W w H c k u hu hsurj T t b ht g hg ≫
      (fullInteriorSourceMap f hL d V c k).left = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The lift to the original full chart is determined by its entire source map. -/
theorem jointGroundFullInteriorLift_unique
    (l : Z ⟶ (fullInteriorSource f hL d V c k).left)
    (hl : l ≫ (fullInteriorSourceMap f hL d V c k).left = g) :
    l = jointGroundFullInteriorLift f hL d a V W w H c k u hu hsurj T t b ht g hg := by
  apply (cancel_mono (U).ι).mp
  exact hl.trans
    (jointGroundFullInteriorLift_comp f hL d a V W w H c k u hu hsurj T t b ht g hg).symm

end FLT.Mazur.HilbertChart.AffineRestriction
