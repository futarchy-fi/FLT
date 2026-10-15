/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertClosedConnectedCertificate
public import FLT.Mazur.AffineHilbertFiniteEnvelopePicard

/-!
# Original finite Picard kernels from closed connected geometry

The full envelope isomorphism is constructed from a connected source and
one connected independent fiber. Consequently the ORIGINAL finite model
has the entire original Picard relation as its kernel, on arbitrary scheme
tests. Global coverage by charts with these hypotheses is not asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  [UniversallyClosed V.hom] (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left] [PreconnectedSpace A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  [UniversallyClosed (snd f hL d V c k).left]
  (x : A.left)
  (hc : _root_.IsPreconnected ((prod.fst : prod A V ⟶ A).left ⁻¹' {x}))
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k

include x hc in
/-- The complete original scheme relation is the kernel of the unchanged finite model. -/
theorem closedConnected_finiteKernel_isPullback :
    IsPullback (p).left (q).left (v).left (v).left := by
  let _ := toEnvelope_isIso_of_closed_connected_fiber f hL d V c k x hc
  exact finiteEnvelope_isPullback f hL d V c k

include x hc in
/-- Original finite coefficients detect actual Picard equality on every scheme test. -/
theorem closedConnected_picard_coefficients_iff {T : Over (Spec (.of R))} (a b : T ⟶ A) :
    (relativeFppfSheaf f).obj.map a.op (sectionAt f hL d V c k) =
        (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) ↔
      ∀ s ∈ finiteKernelCoefficients f hL d V c k,
        a.left.appTop s.val = b.left.appTop s.val := by
  let _ := toEnvelope_isIso_of_closed_connected_fiber f hL d V c k x hc
  exact finiteEnvelope_picard_coefficients_iff f hL d V c k a b

include x hc in
/-- Finite coefficient equalities construct the unique full original relation arrow. -/
theorem closedConnected_coefficients_lift {T : Over (Spec (.of R))} (a b : T ⟶ A)
    (hab : ∀ s ∈ finiteKernelCoefficients f hL d V c k,
      a.left.appTop s.val = b.left.appTop s.val) :
    ∃! z : T ⟶ relation f hL d V c k, z ≫ p = a ∧ z ≫ q = b := by
  let _ := toEnvelope_isIso_of_closed_connected_fiber f hL d V c k x hc
  exact finiteEnvelope_coefficients_lift f hL d V c k a b hab

end FLT.Mazur.HilbertChart.AffineRestriction
