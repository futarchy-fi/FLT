/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertPrincipalInvariantNorm
public import FLT.Mazur.HilbertNestedNormSupport

/-!
# Admissible norm coefficients on actual orbit-principal sources

Restrict the original principal coefficient to the good open and take its
constructed invariant norm. Its support lies in the NEW principal chart's
full-fiber interior. Whole-orbit containment proves nonvanishing at the retained point.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left] (r : Γ(A.left, ⊤))
  (hr : A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k)
/-- The original translation structural algebra for admissible coefficients. -/
local instance admissibleNormTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
local notation "u" => fullInteriorSourceMap f hL d V c k
local notation "v" => orbitPrincipalToInterior f hL d V c k r hr
local notation "l" => fullInteriorChart f hL d V c k
local notation "k'" => orbitPrincipalChart f d V k r

/-- The actual inclusion into the full good open is an open immersion. -/
instance orbitPrincipalToInterior_isOpenImmersion : IsOpenImmersion (v).left :=
  inferInstanceAs (IsOpenImmersion (A.left.homOfLE hr))

omit [IsAffine V.left] [Etale V.hom] in
/-- Composing both open inclusions recovers the original principal source map. -/
@[reassoc]
theorem orbitPrincipalToInterior_source : v ≫ u = orbitPrincipalSourceMap (A := A) r := by
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι A.left hr

/-- The actual restricted principal coefficient, on the possibly nonaffine good open. -/
def orbitPrincipalInteriorSection : Γ((fullInteriorSource f hL d V c k).left, ⊤) :=
  (u).left.appTop r

omit [IsAffine V.left] [Etale V.hom] in
/-- Its nonzero locus is contained in the actual principal source inclusion. -/
theorem orbitPrincipalInteriorSection_support :
    (fullInteriorSource f hL d V c k).left.basicOpen
      (orbitPrincipalInteriorSection f hL d V c k r) ≤ (v).left.opensRange := by
  rw [orbitPrincipalInteriorSection, ← Scheme.preimage_basicOpen_top]
  intro x hx
  refine ⟨⟨x.val, hx⟩, ?_⟩
  change A.left.homOfLE hr ⟨x.val, hx⟩ = x
  rw [Scheme.homOfLE_apply']
  rfl

/-- The coefficient in the original invariant ring is now a specific constructed norm. -/
def orbitPrincipalAdmissibleNorm :
    compatibleFunctions (fst f hL d V c k').left (snd f hL d V c k').left :=
  orbitPrincipalInvariantNorm f hL d V c k r hr b
    (orbitPrincipalInteriorSection f hL d V c k r)

/-- Its nonzero locus lies in the full-fiber interior of the NEW principal chart. -/
theorem orbitPrincipalAdmissibleNorm_support :
    (orbitPrincipalSource r).left.basicOpen
      (orbitPrincipalAdmissibleNorm f hL d V c k r hr b).val ≤
        fullEnvelopeInterior f hL d V c k' := by
  change (orbitPrincipalSource r).left.basicOpen ((v).left.appTop
    (fullEnvelopeRegularNorm f hL d V c l b (orbitPrincipalInteriorSection f hL d V c k r)))
      ≤ fullEnvelopeInterior f hL d V c k'
  have h := nestedNorm_basicOpen_le_fullInterior f hL d V c l v b
    (orbitPrincipalInteriorSection f hL d V c k r)
    (orbitPrincipalInteriorSection_support f hL d V c k r hr)
  simpa only [orbitPrincipalToInterior_chart] using h

/-- Membership in the actual invariant denominator ideal is proved from full-fiber support. -/
theorem orbitPrincipalAdmissibleNorm_mem :
    orbitPrincipalAdmissibleNorm f hL d V c k r hr b ∈
      invariantEnvelopeDenominators f hL d V c k' :=
  (invariantDenominator_iff_fullEnvelopeInterior f hL d V c k' _).mpr
    (orbitPrincipalAdmissibleNorm_support f hL d V c k r hr b)

/-- Whole-orbit containment makes the constructed admissible norm nonzero at the chosen point. -/
theorem orbitPrincipalAdmissibleNorm_nonvanishing (x : (orbitPrincipalSource r).left)
    (horbit : ∀ z : (relation f hL d V c k).left,
      (snd f hL d V c k).left z = x.val → (fst f hL d V c k).left z ∈ A.left.basicOpen r) :
    x ∈ (orbitPrincipalSource r).left.basicOpen
      (orbitPrincipalAdmissibleNorm f hL d V c k r hr b).val := by
  change x ∈ (orbitPrincipalSource r).left.basicOpen ((v).left.appTop
    (fullEnvelopeRegularNorm f hL d V c l b (orbitPrincipalInteriorSection f hL d V c k r)))
  rw [← Scheme.preimage_basicOpen_top]
  apply (mem_basicOpen_fullEnvelopeNorm_iff f hL d V c l b _ _).mpr
  intro z hz
  unfold fullInteriorChart at z hz ⊢
  let z₀ := (nestedToFullRelation f hL d V c k u).left z
  have hp := congrArg (fun t ↦ t.left z) (nestedToFullRelation_fst f hL d V c k u)
  have hq := congrArg (fun t ↦ t.left z) (nestedToFullRelation_snd f hL d V c k u)
  change (fst f hL d V c k).left z₀ =
    (u).left ((fst f hL d V c (u ≫ k)).left z) at hp
  change (snd f hL d V c k).left z₀ =
    (u).left ((snd f hL d V c (u ≫ k)).left z) at hq
  rw [hz] at hq
  rw [orbitPrincipalInteriorSection, ← Scheme.preimage_basicOpen_top]
  change (u).left ((fst f hL d V c (u ≫ k)).left z) ∈ A.left.basicOpen r
  rw [← hp]
  apply horbit z₀
  exact hq.trans (congrArg (fun t ↦ t.left x)
    (orbitPrincipalToInterior_source f hL d V c k r hr))

end FLT.Mazur.HilbertChart.AffineRestriction
