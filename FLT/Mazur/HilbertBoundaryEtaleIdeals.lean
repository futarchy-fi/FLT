/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertInteriorFiniteEquations
public import FLT.Mazur.EnvelopeBoundaryIdealSheaf

/-!
# Exact original Hilbert boundary ideals on all relation tests

Both full original endpoints are etale. The finite boundary equations
therefore generate the same ideal on every affine test of the full
relation, including nonreduced tests. Ideal-sheaf invariance is proved on
smooth charts first, then pulled back along arbitrary test morphisms.
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
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)

/-- The whole original boundary ideal agrees along the two independent etale endpoints. -/
theorem originalBoundaryIdeal_relation_eq {Z : Scheme} [IsAffine Z]
    (z : Z ⟶ (relation f hL d V c k).left) :
    (denominatorIdeal (π).appTop.hom O).map (z ≫ p).appTop.hom =
      (denominatorIdeal (π).appTop.hom O).map (z ≫ q).appTop.hom := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  exact map_denominator_test_eq π O p q
    (fullEnvelopeInterior_invariant f hL d V c k) z

/-- The finite original equations generate equal ideals on every affine relation test. -/
theorem originalEquations_relation_span_eq {Z : Scheme} [IsAffine Z]
    (z : Z ⟶ (relation f hL d V c k).left) :
    Ideal.span ((z ≫ p).appTop.hom ''
      (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))) =
    Ideal.span ((z ≫ q).appTop.hom ''
      (originalInteriorEquations f hL d V c k : Set Γ(A.left, ⊤))) := by
  rw [← Ideal.map_span, ← Ideal.map_span, originalInteriorEquations_span]
  exact originalBoundaryIdeal_relation_eq f hL d V c k z

end FLT.Mazur.HilbertChart.AffineRestriction
