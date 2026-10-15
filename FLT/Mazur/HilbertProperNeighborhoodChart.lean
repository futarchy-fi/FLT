/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperNeighborhoodGroundInterior
public import FLT.Mazur.AffineHilbertFullInteriorChart

/-!
# Original Hilbert charts from constructed proper translation neighborhoods

Proper neighborhoods of all excluded changed translation coordinates replace
the supplied partial chart family. Original full fibers and local reachability
then construct the actual original full-interior chart and its coefficients.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeTranslationNorm SchemeEffectiveEpiSections
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
  [IsAffine B.left] [IsAffine W.left]
  (u : (Over.map a).obj B ⟶ A) (hu : IsOpenMap u.left)
  (hproper : ∀ y : (prod B W).left,
    (fixedBaseEnvelopeMap a V W w u).left y ∉ (toEnvelope f hL d V c k).left.opensRange →
      (prod.snd : prod B W ⟶ W).left y ∈ ProperNeighborhoodAtlas.locus W.hom)
local notation "U" => fullEnvelopeInterior f hL d V c k
local notation "i" => fullInteriorSourceMap f hL d V c k
local notation "l" => fullInteriorChart f hL d V c k

include H hu hproper

/-- Canonical proper charts and one independent lift place a full fiber in the original open. -/
theorem fullEnvelopeInterior_of_properNeighborhoods (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) (hlift : x ∈ Set.range u.left) : x ∈ U :=
  mem_originalFullInterior_of_affineProperNeighborhoods a V W w H u
    (toEnvelope f hL d V c k).left.opensRange hproper hu x hx hlift

/-- The actual restricted original chart has a nonvanishing admissible invariant coefficient. -/
theorem exists_fullInterior_coefficient_of_properNeighborhoods [Etale V.hom] (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) (hlift : x ∈ Set.range u.left) :
    ∃ y : (fullInteriorSource f hL d V c k).left,
      ∃ r : compatibleFunctions (fst f hL d V c l).left (snd f hL d V c l).left,
        (i).left y = x ∧ r ∈ invariantEnvelopeDenominators f hL d V c l ∧
          y ∈ (fullInteriorSource f hL d V c k).left.basicOpen r.val := by
  let y : (fullInteriorSource f hL d V c k).left :=
    ⟨x, fullEnvelopeInterior_of_properNeighborhoods f hL d a V W w H c k u hu hproper
      x hx hlift⟩
  obtain ⟨r, hr, hyr⟩ := fullInteriorChart_nonvanishing f hL d V c k y
  exact ⟨y, r, rfl, hr, hyr⟩

variable {Z : Scheme} (g : Z ⟶ A.left)
  (hg : Set.range g ⊆ fullEnvelopeLocus f hL d V c k)
  (hlift : Set.range g ⊆ Set.range u.left)

/-- Pointwise reachability lifts a whole original scheme test into its full-interior chart. -/
def properNeighborhoodFullInteriorLift : Z ⟶ (fullInteriorSource f hL d V c k).left := by
  change Z ⟶ (U).toScheme
  apply IsOpenImmersion.lift (U).ι g
  rw [Scheme.Opens.range_ι]
  intro x hx
  exact fullEnvelopeInterior_of_properNeighborhoods f hL d a V W w H c k u hu hproper
    x (hg hx) (hlift hx)

/-- The lift retains the complete original scheme morphism, including nilpotents. -/
@[reassoc]
theorem properNeighborhoodFullInteriorLift_comp :
    properNeighborhoodFullInteriorLift f hL d a V W w H c k u hu hproper g hg hlift ≫
      (i).left = g := IsOpenImmersion.lift_fac _ _ _

/-- The constructed chart morphism is independent of all pointwise choices of ground lifts. -/
theorem properNeighborhoodFullInteriorLift_unique
    (j : Z ⟶ (fullInteriorSource f hL d V c k).left) (hj : j ≫ (i).left = g) :
    j = properNeighborhoodFullInteriorLift f hL d a V W w H c k u hu hproper g hg hlift := by
  apply (cancel_mono (U).ι).mp
  exact hj.trans (properNeighborhoodFullInteriorLift_comp
    f hL d a V W w H c k u hu hproper g hg hlift).symm

end FLT.Mazur.HilbertChart.AffineRestriction
