/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.InvariantFiniteFreeTraceUnit
public import FLT.Mazur.HilbertFiniteDomainBoundaryTrace

/-!
# Original Hilbert boundary surjectivity on full finite free domains

When the entire original relation admits a finite basis on the chosen affine
orbit domain, its trace ideal is one and the unchanged boundary section map
is surjective. No invertibility assumption on the degree is needed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit InvariantOpenRelationDiagram
open SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency true
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "eo" => equivalence f hL d V c k
variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
set_option quotPrecheck false
local notation "E" => (pullOpen eo W).val
local notation "Ω" => (invariantSheaf eo).obj.obj (op W)
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
local notation "Wc" => (TopologicalSpace.Opens.map (m).base).obj W
local notation "D" => (invariantSheaf ec).obj.obj (op Wc)
local notation "ρ" => originalClosedSectionPullback f hL d V c k W
attribute [local irreducible] relation fst snd equivalence invariantSheaf
  originalClosedEquivalence originalClosedInvariantMap originalClosedSectionPullback
variable (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
  (hfin : (pullOpen (equivalence f hL d V c k) W).val ≤
    finiteTargetOpen (fst f hL d V c k).left)

variable {ι : Type} [Finite ι]

/-- Endpoint spanning and étaleness make the original Hilbert trace ideal a unit ideal. -/
theorem originalFiniteDomainTraceIdeal_eq_top_of_basis :
    let _ := (InvariantOpenRelationDiagram.fst p E).left.appTop.hom.toAlgebra
    Module.Basis ι Γ((source E).left, ⊤)
      Γ((InvariantOpenRelationDiagram.relation p E).left, ⊤) →
        originalFiniteDomainTraceIdeal f hL d V c k W hW hfin = ⊤ := by
  let _ := (InvariantOpenRelationDiagram.fst p E).left.appTop.hom.toAlgebra
  dsimp only
  intro basis
  exact finiteDomainTraceIdeal_eq_top_of_basis eo W
    (fullRelationSchemeEquivalence f hL d V c k) hW hfin basis

include hW hfin in
/-- The exact original closed invariant section map is surjective on these full domains. -/
theorem originalClosedSectionPullback_surjective_of_full_basis :
    let _ := (InvariantOpenRelationDiagram.fst p E).left.appTop.hom.toAlgebra
    Module.Basis ι Γ((source E).left, ⊤)
      Γ((InvariantOpenRelationDiagram.relation p E).left, ⊤) →
        Function.Surjective ρ := by
  let _ := (InvariantOpenRelationDiagram.fst p E).left.appTop.hom.toAlgebra
  dsimp only
  intro basis
  exact originalClosedSectionPullback_surjective_of_traceIdeal f hL d V c k W hW hfin
    (originalFiniteDomainTraceIdeal_eq_top_of_basis f hL d V c k W hW hfin basis)

end FLT.Mazur.HilbertChart.AffineRestriction
