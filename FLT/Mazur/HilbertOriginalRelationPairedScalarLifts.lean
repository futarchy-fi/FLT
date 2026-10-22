/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationPairedAffineDomain
public import FLT.Mazur.HilbertOriginalRelationPairedInvariantLifts
public import FLT.Mazur.HilbertSubframeOriginalScalars

/-!
# Paired residual frames over the original section-ring domain

Both endpoints of an original rank-stage test lift to a stable affine chart
inside the prescribed invariant open. This constructs the hypotheses for the
existing original section-ring scalar homomorphism, without replacing its
source by all invariants. Full invariant agreement uses the original arrow.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open FiniteGroupRestriction SchemeFiniteGroupQuotient
open RelativeRelationOrbit InvariantOpenRelationDiagram
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] EquivalenceRelationNormalizedFrames.source
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd
variable (n : ℕ) (o : Fin n)
variable (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)

local notation "kS" => U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "D" => SchemeRelationRestriction.doubleDomain p q kS
local notation "F" => SchemeRelationRestriction.fst p q kS
local notation "H" => SchemeRelationRestriction.snd p q kS

open RelativeOrderedTuples
local notation "endpoint" => F ≫ kS
local instance pairedScalarDomainOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance pairedScalarDomainOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance pairedScalarDomainOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- A paired residual chart remains over the prescribed original invariant section ring. -/
theorem exists_originalRelation_rankStage_scalar_lifts
    (O : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
    (m order : ℕ) (o' : Fin m)
    (z : rankPullbackThickening (Over.mk p) endpoint m order)
    (hzO : endpoint (rankPullbackMap (Over.mk p) endpoint m order z) ∈
      (pullOpen (equivalence f hL d V c k) O).val) :
    ∃ (W : (normalizedFullRelationFrames f hL d V c k m o').Opens)
      (T : Scheme.{0}) (a b : T ⟶ W.toScheme)
      (v : T ⟶ rankPullbackThickening (Over.mk p) endpoint m order) (t : T)
      (hW : ∀ g : Equiv.Perm (Fin m),
        (normalizedFullRelationAction f hL d V c k m o' g).hom ⁻¹ᵁ W = W)
      (hWO : W ≤ normalizedFullRelationFirst f hL d V c k m o' ⁻¹ᵁ
        (pullOpen (equivalence f hL d V c k) O).val),
      IsAffineOpen W ∧ IsAffine T ∧ Etale v ∧ v t = z ∧
      a ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' =
        v ≫ rankPullbackMap (Over.mk p) endpoint m order ≫ endpoint ∧
      b ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' =
        v ≫ rankPullbackMap (Over.mk p) endpoint m order ≫ H ≫ kS ∧
      (∀ s : invariantCoordinates
        (restrictedAction (normalizedFullRelationAction f hL d V c k m o') W hW),
        a.appTop s.val = b.appTop s.val) ∧
      ∀ s : (invariantSheaf (equivalence f hL d V c k)).obj.obj (op O),
        a.appTop (normalizedOriginalScalarMap f hL d V c k m o' O W hW hWO s).val =
          b.appTop (normalizedOriginalScalarMap f hL d V c k m o' O W hW hWO s).val := by
  let E := (pullOpen (equivalence f hL d V c k) O).val
  have hE : (p) ⁻¹ᵁ E = (q) ⁻¹ᵁ E := pullOpen_preimage_eq (equivalence f hL d V c k) O
  let l := rankPullbackMap (Over.mk p) endpoint m order
  have hyO : (l ≫ H ≫ kS) z ∈ E := by
    have h := (congrArg (fun B ↦ SchemeRelationRestriction.arrow p q kS (l z) ∈ B)
      hE).to_iff
    have hx : (p) (SchemeRelationRestriction.arrow p q kS (l z)) ∈ E := by
      change (SchemeRelationRestriction.arrow p q kS ≫ p) (l z) ∈ E
      rw [SchemeRelationRestriction.arrow_fst]
      exact hzO
    have hy := h.mp hx
    change (SchemeRelationRestriction.arrow p q kS ≫ q) (l z) ∈ E at hy
    rw [SchemeRelationRestriction.arrow_snd] at hy
    exact hy
  let _ := finTuples_affine (firstRelationEnvelope (A := A) V) m
  obtain ⟨W, T, a, b, v, t, hWaff, hT, hv, ht, hWO, hW, ha, hb⟩ :=
    exists_paired_affine_endpoint_lifts_within e m o'
      (normalizedOriginalFrameInclusion f hL d V c k m o')
      (fullRelationOrderedEnvelopeMap f hL d V c k m)
      (l ≫ endpoint) (l ≫ H ≫ kS) E hE (by
        rintro _ ⟨w, rfl⟩
        exact rankPullback_endpoint (Over.mk p) endpoint m order w)
      (originalRelation_rankStage_second_exactRank f hL d V c k n o U m order) z hzO hyO
  have ha' : a ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' =
      v ≫ l ≫ endpoint := ha
  have hb' : b ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' =
      v ≫ l ≫ H ≫ kS := hb
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let δ := v ≫ l ≫ SchemeRelationRestriction.arrow p q kS
  have hp : δ ≫ p = a ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' := by
    dsimp only [δ]
    rw [Category.assoc, Category.assoc, SchemeRelationRestriction.arrow_fst, ha']
  have hq : δ ≫ q = b ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o' := by
    dsimp only [δ]
    rw [Category.assoc, Category.assoc, SchemeRelationRestriction.arrow_snd, hb']
  have heq := invariant_eq_of_exactRank_original_arrow e m o' W hW a b δ hp hq (by
    change Set.range (a ≫ W.ι ≫ normalizedFullRelationFirst f hL d V c k m o') ⊆ _
    rw [ha']
    rintro _ ⟨w, rfl⟩
    exact rankPullback_endpoint (Over.mk p) endpoint m order (v w))
  exact ⟨W, T, a, b, v, t, hW, hWO, hWaff, hT, hv, ht, ha', hb', heq,
    fun s ↦ heq (normalizedOriginalScalarMap f hL d V c k m o' O W hW hWO s)⟩

end FLT.Mazur.HilbertChart.AffineRestriction
