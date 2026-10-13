/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertAdmissiblePrincipalExistence
public import FLT.Mazur.HilbertInvariantPrincipalProjection

/-!
# Affine quotient neighborhoods of original full-interior points

The constructed nonvanishing admissible norm supplies an affine scheme open
chart containing the original quotient point. Initial full-interior coverage
of all quotient points is a separate geometric task.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation RelativeRelationOrbit
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom] [Surjective V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] (k : A ⟶ variableHilbertTest f d V)
  [IsOpenImmersion k.left]
/-- The basis is for the unchanged original translation algebra. -/
local instance quotientNormTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
local notation "e" => variableChartEquivalenceRelation f hL d V c

include b
/-- An original full-interior point has a constructed affine open scheme quotient neighborhood. -/
theorem exists_fullInterior_affine_quotient_chart (x : A.left)
    (hx : x ∈ fullEnvelopeInterior f hL d V c k) :
    ∃ (Q : Scheme) (q : Q.toLocallyRingedSpace ⟶ invariantLocallyRingedSpace e),
      IsAffine Q ∧ LocallyRingedSpace.IsOpenImmersion q ∧
        projection e (k.left x) ∈ Set.range q.base := by
  obtain ⟨r, hr, _, s, hs, hx'⟩ :=
    exists_fullInterior_admissible_principal f hL d V c k b x hx
  let l := orbitPrincipalChart f d V k r
  let Q := invariantPrincipalQuotientScheme f hL d V c l s hs
  let q := invariantPrincipalOpenChart f hL d V c l s hs
  refine ⟨Q, q, ?_, inferInstance, ?_⟩
  · let _ := invariantPrincipal_toEnvelope_isIso f hL d V c l s hs
    exact fullEnvelopeTarget_affine f hL d V c (invariantPrincipalChart f hL d V c l s)
  · have h := invariantPrincipalOpenChart_contains f hL d V c l s hs ⟨x, hr⟩ hx'
    convert h using 1
    congr 1
    unfold l orbitPrincipalChart orbitPrincipalSourceMap
    rfl

end FLT.Mazur.HilbertChart.AffineRestriction
