/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryQuotientNilpotence
public import FLT.Mazur.HilbertBoundaryRelationNilpotence
public import FLT.Mazur.RelativeRelationNilpotentGerms
public import FLT.Mazur.ClosedRelationOrbitEmbedding

/-!
# The original quotient tower: topology and nilpotent germs

Every whole quotient transition is a homeomorphism on underlying spaces.
Its structure-sheaf kernel has the original target-order power bound on all
opens and all stalks. The sheaf maps are not asserted surjective, so these
results do not claim closed immersions of schemes or scheme effectivity.
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
local notation "I" => boundaryIdealSheaf π O
local notation "B" n:max => originalThickenedSource f hL d V c k n
local notation "i" n:max => originalThickenedSourceMap f hL d V c k n
local notation "C" n:max => originalThickenedRelation f hL d V c k n
local notation "r" n:max => originalThickenedFst f hL d V c k n
local notation "s" n:max => originalThickenedSnd f hL d V c k n
local notation "z" n:max => originalThickenedArrow f hL d V c k n

open RelativeRelationOrbit
local notation "Q" n:max => locallyRingedQuotient (p := r n) (q := s n)
local notation "P" n:max => locallyRingedProjection (p := r n) (q := s n)
local notation "Q₀" => locallyRingedQuotient
  (p := fst f hL d V c k) (q := snd f hL d V c k)
local notation "P₀" => locallyRingedProjection
  (p := fst f hL d V c k) (q := snd f hL d V c k)

attribute [local irreducible] originalThickenedSource originalThickenedSourceMap
  originalThickenedRelation originalThickenedFst originalThickenedSnd originalThickenedArrow

local notation "e" n:max => originalThickenedEquivalence f hL d V c k n

variable {m n : ℕ} (h : m ≤ n)

local notation "t" => originalThickenedInvariantTransition f hL d V c k h
local notation "j" => originalThickenedTransition f hL d V c k h
local notation "a" => originalThickenedRelationTransition f hL d V c k h

/-- The whole quotient transition has the closed orbit comparison as its actual point map. -/
theorem originalThickenedInvariantTransition_isClosedEmbedding :
    Topology.IsClosedEmbedding (t).base := by
  have he : ⇑(t).base = closedOrbitMap (e n) (e m) j a
      (originalThickenedRelationTransition_fst f hL d V c k h)
      (originalThickenedRelationTransition_snd f hL d V c k h) := by
    funext x
    obtain ⟨y, rfl⟩ := projection_surjective (e m) x
    exact invariantMap_projection_apply (e n) (e m) (j).left (a).left _ _ y
  rw [he]
  exact closedOrbitMap_isClosedEmbedding (e n) (e m) j a
    (originalThickenedRelationTransition_fst f hL d V c k h)
    (originalThickenedRelationTransition_snd f hL d V c k h)
    (originalThickenedRelationTransition_fst_isPullback f hL d V c k h)

/-- Every original quotient point is retained across every nilpotent transition. -/
theorem originalThickenedInvariantTransition_surjective : Function.Surjective (t).base := by
  intro x
  obtain ⟨y, rfl⟩ := projection_surjective (e n) x
  obtain ⟨v, rfl⟩ := originalThickenedTransition_surjective f hL d V c k h y
  exact ⟨projection (e m) v,
    invariantMap_projection_apply (e n) (e m) (j).left (a).left _ _ v⟩

/-- The full quotient topology is unchanged, while nilpotent regular functions are retained. -/
theorem originalThickenedInvariantTransition_isHomeomorph :
    IsHomeomorph (t).base :=
  isHomeomorph_iff_isEmbedding_surjective.mpr
    ⟨(originalThickenedInvariantTransition_isClosedEmbedding f hL d V c k h).isEmbedding,
      originalThickenedInvariantTransition_surjective f hL d V c k h⟩

/-- Every quotient open has the power bound, with no affine source-domain hypothesis. -/
theorem originalThickenedInvariantTransition_section_pow_eq_zero
    (W : TopologicalSpace.Opens (Orbit (e n)))
    (v : (invariantSheaf (e n)).obj.obj (op W)) (hv : (t).c.app (op W) v = 0) :
    v ^ (n + 1) = 0 :=
  invariantMap_section_pow_eq_zero_on (e n) (e m) (j).left (a).left _ _ (n + 1)
    (originalThickenedTransition_ker_pow f hL d V c k h) W v hv

/-- At every quotient point, all germs in the transition kernel obey the same explicit bound. -/
theorem originalThickenedInvariantTransition_stalk_pow_eq_zero
    (x : invariantLocallyRingedSpace (e m))
    (v : (invariantLocallyRingedSpace (e n)).presheaf.stalk ((t).base x))
    (hv : (t).stalkMap x v = 0) : v ^ (n + 1) = 0 :=
  invariantMap_stalk_pow_eq_zero (e n) (e m) (j).left (a).left _ _ (n + 1)
    (originalThickenedTransition_ker_pow f hL d V c k h)
    (originalThickenedInvariantTransition_isClosedEmbedding f hL d V c k h).isEmbedding.isInducing
    x v hv

end FLT.Mazur.HilbertChart.AffineRestriction
