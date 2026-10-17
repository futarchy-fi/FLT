/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryLocalCoverCriterion
public import FLT.Mazur.RelativeRelationPulledIdealCover

/-!
# Finite equations on the actual ambient boundary source

The original closed immersion supplies a surjective restriction with finite
kernel on each affine source domain. Both source rings are Noetherian.
These are ambient source rings; no finiteness over invariant scalars follows.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "O" => Scheme.Hom.opensRange (Over.Hom.left (toEnvelope f hL d V c k))
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

open RelativeRelationOrbit
local notation "e" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence

local notation "m" => originalClosedInvariantMap f hL d V c k

set_option quotPrecheck false
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "Q" => (sourceSheaf e).obj.obj (op W)
local notation "T" => (sourceSheaf ec).obj.obj (op Wc)

/-- Restriction on the entire original source, before imposing the relation equations. -/
def originalAmbientBoundaryRestriction : Q →+* T :=
  closedSourceRestriction e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W

attribute [local irreducible] originalAmbientBoundaryRestriction

/-- Every boundary source function has an ambient lift on an affine source domain. -/
theorem originalAmbientBoundaryRestriction_surjective
    (hW : IsAffineOpen (pullOpen e W).val) :
    Function.Surjective (originalAmbientBoundaryRestriction f hL d V c k W) := by
  unfold originalAmbientBoundaryRestriction
  exact closedSourceRestriction_surjective e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W hW

omit [IsAffine A.left] in
/-- The ambient source ring is Noetherian by the actual selected Hilbert geometry. -/
theorem originalAmbientSource_noetherian
    (hW : IsAffineOpen (pullOpen e W).val) : IsNoetherianRing Q := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact IsLocallyNoetherian.component_noetherian ⟨_, hW⟩

/-- The closed boundary source ring is Noetherian, without a quotient finiteness assumption. -/
theorem originalAmbientBoundary_noetherian
    (hW : IsAffineOpen (pullOpen e W).val) : IsNoetherianRing T := by
  let _ := originalAmbientSource_noetherian f hL d V c k W hW
  exact isNoetherianRing_of_surjective Q T
    (originalAmbientBoundaryRestriction f hL d V c k W)
    (originalAmbientBoundaryRestriction_surjective f hL d V c k W hW)

/-- The actual ambient boundary kernel has finitely many equations. -/
theorem originalAmbientBoundary_kernel_fg
    (hW : IsAffineOpen (pullOpen e W).val) :
    (RingHom.ker (originalAmbientBoundaryRestriction f hL d V c k W)).FG := by
  let _ := originalAmbientSource_noetherian f hL d V c k W hW
  exact IsNoetherian.noetherian _

/-- Ambient restriction agrees exactly with the invariant-section pullback. -/
theorem originalAmbientBoundaryRestriction_invariant
    (a : (invariantSheaf e).obj.obj (op W)) :
    originalAmbientBoundaryRestriction f hL d V c k W
        ((invariantInclusion e).hom.app (op W) a) =
      (invariantInclusion ec).hom.app (op Wc)
        (originalClosedSectionPullback f hL d V c k W a) := by
  unfold originalAmbientBoundaryRestriction originalClosedSectionPullback
  exact (invariantMap_source_apply e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W a).symm

end FLT.Mazur.HilbertChart.AffineRestriction
