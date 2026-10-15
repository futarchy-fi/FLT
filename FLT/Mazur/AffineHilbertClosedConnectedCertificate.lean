/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertClopenAdmissible
public import FLT.Mazur.AffineHilbertConnectedEnvelopeFiber
public import FLT.Mazur.AffineHilbertGenericEnvelopeCriterion

/-!
# Initial original finite-model certificates from closed connected geometry

A connected independent fiber supplies a full-fiber point by reflexivity.
Closed endpoint geometry then constructs an original nonzero invariant
coefficient. On integral sources this yields a represented original Picard
region and proves the whole generic-envelope condition. No initial fullness
or admissibility is assumed; closedness and connectedness remain explicit
geometric hypotheses which arbitrary original charts need not satisfy.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  [UniversallyClosed V.hom] (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  [UniversallyClosed (snd f hL d V c k).left]
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)

/-- Connected-fiber geometry constructs nonzero ORIGINAL admissibility at the chosen point. -/
theorem denominators_ne_bot_of_closed_connected_fiber (x : A.left)
    (hc : _root_.IsPreconnected (π ⁻¹' {x})) :
    invariantEnvelopeDenominators f hL d V c k ≠ ⊥ :=
  closedEnvelope_denominators_ne_bot f hL d V c k x
    (fullEnvelopeLocus_of_connected_fiber f hL d V c k x hc)

/-- On an integral original source, one connected fiber constructs a represented Picard region. -/
theorem picardTarget_nonempty_of_closed_connected_fiber [IsIntegral A.left] (x : A.left)
    (hc : _root_.IsPreconnected (π ⁻¹' {x})) :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left :=
  finiteModelPicardFppfTarget_nonempty_of_denominators_ne_bot f hL d V c k
    (denominators_ne_bot_of_closed_connected_fiber f hL d V c k x hc)

/-- The initial generic-envelope certificate is proved, not supplied, in this geometric case. -/
theorem genericEnvelope_of_closed_connected_fiber [IsIntegral A.left] (x : A.left)
    (hc : _root_.IsPreconnected (π ⁻¹' {x})) :
    ∀ z : (prod A V).left,
      oldEnvelopeProjection f hL d V c k z =
          genericPoint (finiteKernelModel f hL d V c k).left →
        z ∈ (toEnvelope f hL d V c k).left.opensRange :=
  (denominators_ne_bot_iff_generic_envelope f hL d V c k).mp
    (denominators_ne_bot_of_closed_connected_fiber f hL d V c k x hc)

omit [IsAffine A.left] in
/-- On a connected source, one connected fiber forces fullness on the whole source. -/
theorem fullInterior_eq_top_of_closed_connected_fiber [PreconnectedSpace A.left]
    (x : A.left) (hc : _root_.IsPreconnected (π ⁻¹' {x})) :
    fullEnvelopeInterior f hL d V c k = ⊤ := by
  apply SetLike.coe_injective
  have hU : IsClopen (fullEnvelopeInterior f hL d V c k : Set A.left) :=
    ⟨fullEnvelopeInterior_isClosed f hL d V c k,
      (fullEnvelopeInterior f hL d V c k).isOpen⟩
  apply hU.eq_univ
  refine ⟨x, ?_⟩
  rw [fullEnvelopeInterior_eq_locus]
  exact fullEnvelopeLocus_of_connected_fiber f hL d V c k x hc

omit [IsAffine A.left] in
/-- Closed connected geometry constructs the full envelope isomorphism on a connected source. -/
theorem toEnvelope_isIso_of_closed_connected_fiber [PreconnectedSpace A.left]
    (x : A.left) (hc : _root_.IsPreconnected (π ⁻¹' {x})) :
    IsIso (toEnvelope f hL d V c k).left := by
  apply (invariantEnvelopeDenominators_eq_top_iff f hL d V c k).mp
  rw [Ideal.eq_top_iff_one, invariantDenominator_iff_fullEnvelopeInterior,
    fullInterior_eq_top_of_closed_connected_fiber f hL d V c k x hc]
  exact le_top

/-- Fiberwise connectedness gives original coefficient coverage at every source point. -/
theorem originalCoverage_of_closed_connected_fibers
    (hc : ∀ x : A.left, _root_.IsPreconnected (π ⁻¹' {x})) (x : A.left) :
    ∃ s : SchemeEffectiveEpiSections.compatibleFunctions
        (fst f hL d V c k).left (snd f hL d V c k).left,
      s ∈ invariantEnvelopeDenominators f hL d V c k ∧ x ∈ A.left.basicOpen s.val :=
  (closedEnvelope_admissible_coverage_iff f hL d V c k x).mpr
    (fullEnvelopeLocus_of_connected_fiber f hL d V c k x (hc x))

end FLT.Mazur.HilbertChart.AffineRestriction
