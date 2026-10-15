/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertDegreeFiberCertificate
public import FLT.Mazur.AffineHilbertClopenAdmissible
public import FLT.Mazur.AffineHilbertFiniteEnvelopePicard

/-!
# Original invariant certificates from degree and Picard witnesses

For closed original endpoints, actual equal-class source points and the
translation degree construct a nonvanishing ORIGINAL invariant idempotent.
On a preconnected source this fills the entire envelope, and recovers the
full original finite-model Picard kernel on arbitrary scheme tests. The
independent fibers may be disconnected; existence of the witnesses and
closedness of original endpoints remain explicit geometric hypotheses.
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
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left] [IsFinite V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  [UniversallyClosed (snd f hL d V c k).left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "π" => Over.Hom.left (prod.fst : prod A V ⟶ A)
local notation "σ" => sectionAt f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k

omit [UniversallyClosed (snd f hL d V c k).left] in
/-- Degree at most one recovers the full original kernel without any closed-endpoint premise. -/
theorem degreeOne_finiteKernel_isPullback
    (hn : ∀ x : A.left, V.hom.finrank (A.hom x) ≤ 1) :
    IsPullback (p).left (q).left (v).left (v).left := by
  let _ := toEnvelope_isIso_of_degree_le_one f hL d V c k hn
  exact finiteEnvelope_isPullback f hL d V c k

omit [UniversallyClosed (snd f hL d V c k).left] in
/-- Degree-one source images give original Picard coefficient tests on every scheme test. -/
theorem degreeOne_picard_coefficients_iff
    (hn : ∀ x : A.left, V.hom.finrank (A.hom x) ≤ 1)
    {W : Over (Spec (.of R))} (u w : W ⟶ A) :
    (relativeFppfSheaf f).obj.map u.op σ = (relativeFppfSheaf f).obj.map w.op σ ↔
      ∀ s ∈ finiteKernelCoefficients f hL d V c k,
        u.left.appTop s.val = w.left.appTop s.val := by
  let _ := toEnvelope_isIso_of_degree_le_one f hL d V c k hn
  exact finiteEnvelope_picard_coefficients_iff f hL d V c k u w

/-- One original invariant idempotent detects precisely equality of actual fiber counts. -/
theorem closedEnvelopeCoefficient_nonvanishing_iff_fiber_ncard_eq (x : A.left) :
    x ∈ A.left.basicOpen (closedEnvelopeCoefficient f hL d V c k).val ↔
      ((q).left ⁻¹' {x}).ncard = (π ⁻¹' {x}).ncard := by
  rw [closedEnvelopeCoefficient_nonvanishing_iff, fullEnvelopeLocus_iff_fiber_ncard_eq]

variable {T : Over (Spec (.of R))} (b : T ⟶ A) {n : ℕ}
  (a : Fin n → (T ⟶ A)) (t : T.left)
  (ha : Function.Injective (fun i ↦ (a i).left t))
  (hc : ∀ i, (relativeFppfSheaf f).obj.map (a i).op (sectionAt f hL d V c k) =
    (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k))
  (hn : V.hom.finrank (A.hom (b.left t)) ≤ n)

include ha hc hn in
/-- Degree and actual Picard equalities make the constructed ORIGINAL coefficient nonvanishing. -/
theorem closedDegreePicard_coefficient_nonvanishing :
    b.left t ∈ A.left.basicOpen (closedEnvelopeCoefficient f hL d V c k).val :=
  (closedEnvelopeCoefficient_nonvanishing_iff f hL d V c k (b.left t)).mpr
    (fullEnvelopeLocus_of_degree_picard_witnesses f hL d V c k b a t ha hc hn)

include ha hc hn in
/-- Original nonzero admissibility is constructed without connected independent fibers. -/
theorem closedDegreePicard_denominators_ne_bot :
    invariantEnvelopeDenominators f hL d V c k ≠ ⊥ :=
  closedEnvelope_denominators_ne_bot f hL d V c k (b.left t)
    (fullEnvelopeLocus_of_degree_picard_witnesses f hL d V c k b a t ha hc hn)

variable [PreconnectedSpace A.left]

omit [IsAffine A.left] in
include ha hc hn in
/-- A single degree certificate fills the entire clopen interior on a preconnected source. -/
theorem closedDegreePicard_fullInterior_eq_top :
    fullEnvelopeInterior f hL d V c k = ⊤ := by
  apply SetLike.coe_injective
  have hU : IsClopen (fullEnvelopeInterior f hL d V c k : Set A.left) :=
    ⟨fullEnvelopeInterior_isClosed f hL d V c k,
      (fullEnvelopeInterior f hL d V c k).isOpen⟩
  apply hU.eq_univ
  refine ⟨b.left t, ?_⟩
  rw [fullEnvelopeInterior_eq_locus]
  exact fullEnvelopeLocus_of_degree_picard_witnesses f hL d V c k b a t ha hc hn

omit [IsAffine A.left] in
include ha hc hn in
/-- The whole original envelope isomorphism is derived from the degree and Picard data. -/
theorem closedDegreePicard_toEnvelope_isIso : IsIso (toEnvelope f hL d V c k).left := by
  apply (invariantEnvelopeDenominators_eq_top_iff f hL d V c k).mp
  rw [Ideal.eq_top_iff_one, invariantDenominator_iff_fullEnvelopeInterior,
    closedDegreePicard_fullInterior_eq_top f hL d V c k b a t ha hc hn]
  exact le_top

include ha hc hn in
/-- The unchanged finite model has the entire original Picard relation as its scheme kernel. -/
theorem closedDegreePicard_finiteKernel_isPullback :
    IsPullback (p).left (q).left (v).left (v).left := by
  let _ := closedDegreePicard_toEnvelope_isIso f hL d V c k b a t ha hc hn
  exact finiteEnvelope_isPullback f hL d V c k

include ha hc hn in
/-- Original finite coefficient equations detect Picard equality on arbitrary scheme tests. -/
theorem closedDegreePicard_coefficients_iff {W : Over (Spec (.of R))} (u w : W ⟶ A) :
    (relativeFppfSheaf f).obj.map u.op σ = (relativeFppfSheaf f).obj.map w.op σ ↔
      ∀ s ∈ finiteKernelCoefficients f hL d V c k,
        u.left.appTop s.val = w.left.appTop s.val := by
  let _ := closedDegreePicard_toEnvelope_isIso f hL d V c k b a t ha hc hn
  exact finiteEnvelope_picard_coefficients_iff f hL d V c k u w

end FLT.Mazur.HilbertChart.AffineRestriction
