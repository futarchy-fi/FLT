/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertClosedEnvelopeInterior
public import FLT.Mazur.SchemeIdempotentSupport

/-!
# Original admissible coefficients from closed endpoint geometry

The full independent-envelope interior has an invariant idempotent equation
in the ORIGINAL affine source. This single constructed coefficient covers
all full-fiber points. No initial admissible coefficient, fresh-chart norm,
or generic-envelope fullness is an input.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
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
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "C" => compatibleFunctions p q

/-- The original good interior has an invariant idempotent equation, constructed from geometry. -/
theorem exists_fullInterior_idempotent :
    ∃ e : C, IsIdempotentElem e.val ∧
      A.left.basicOpen e.val = fullEnvelopeInterior f hL d V c k :=
  SchemeIdempotentSupport.exists_invariant_idempotent p q
    (fullEnvelopeInterior f hL d V c k) (fullEnvelopeInterior_isClosed f hL d V c k)
    (fullEnvelopeInterior_invariant f hL d V c k)

/-- One specific ORIGINAL invariant coefficient for the entire full-fiber region. -/
def closedEnvelopeCoefficient : C := (exists_fullInterior_idempotent f hL d V c k).choose

/-- The chosen original coefficient is idempotent even on a nonreduced source. -/
theorem closedEnvelopeCoefficient_idempotent :
    IsIdempotentElem (closedEnvelopeCoefficient f hL d V c k).val :=
  (exists_fullInterior_idempotent f hL d V c k).choose_spec.1

/-- Its support is exactly the constructed full-envelope interior. -/
theorem closedEnvelopeCoefficient_support :
    A.left.basicOpen (closedEnvelopeCoefficient f hL d V c k).val =
      fullEnvelopeInterior f hL d V c k :=
  (exists_fullInterior_idempotent f hL d V c k).choose_spec.2

/-- The coefficient is admissible for the original full relation, not just a seed restriction. -/
theorem closedEnvelopeCoefficient_admissible :
    closedEnvelopeCoefficient f hL d V c k ∈ invariantEnvelopeDenominators f hL d V c k := by
  rw [invariantDenominator_iff_fullEnvelopeInterior, closedEnvelopeCoefficient_support]

/-- Every actual full-fiber point receives the same original admissible coefficient. -/
theorem closedEnvelopeCoefficient_nonvanishing_iff (x : A.left) :
    x ∈ A.left.basicOpen (closedEnvelopeCoefficient f hL d V c k).val ↔
      x ∈ fullEnvelopeLocus f hL d V c k := by
  rw [closedEnvelopeCoefficient_support]
  exact Set.ext_iff.mp (fullEnvelopeInterior_eq_locus f hL d V c k) x

/-- Original admissible coverage is exactly full-fiber coverage in this geometric case. -/
theorem closedEnvelope_admissible_coverage_iff (x : A.left) :
    (∃ s : C, s ∈ invariantEnvelopeDenominators f hL d V c k ∧
      x ∈ A.left.basicOpen s.val) ↔ x ∈ fullEnvelopeLocus f hL d V c k := by
  constructor
  · rintro ⟨s, hs, hx⟩
    have h := (invariantDenominator_iff_fullEnvelopeInterior f hL d V c k s).mp hs hx
    rwa [← fullEnvelopeInterior_eq_locus f hL d V c k]
  · intro hx
    exact ⟨closedEnvelopeCoefficient f hL d V c k,
      closedEnvelopeCoefficient_admissible f hL d V c k,
      (closedEnvelopeCoefficient_nonvanishing_iff f hL d V c k x).mpr hx⟩

/-- A retained point proves nonzero original admissibility, without an integral source. -/
theorem closedEnvelope_denominators_ne_bot (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) :
    invariantEnvelopeDenominators f hL d V c k ≠ ⊥ := by
  obtain ⟨s, hs, hx⟩ := (closedEnvelope_admissible_coverage_iff f hL d V c k x).mpr hx
  apply (Submodule.ne_bot_iff _).mpr
  refine ⟨s, hs, ?_⟩
  intro he
  rw [he] at hx
  change x ∈ A.left.basicOpen 0 at hx
  simp only [Scheme.basicOpen_zero, TopologicalSpace.Opens.mem_bot] at hx

end FLT.Mazur.HilbertChart.AffineRestriction
