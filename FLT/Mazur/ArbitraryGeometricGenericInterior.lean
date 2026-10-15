/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricAffineFullFiber
public import FLT.Mazur.NoetherianEnvelopeGenericInterior
public import FLT.Mazur.VariableHilbertNoetherianSource
public import FLT.Mazur.AffineHilbertFullFiberInterior

/-!
# Original full-interior charts through arbitrary generic-fiber classes

For an irreducible original coefficient scheme, every geometric Picard class
above its generic point has a constructed original affine Hilbert parameter
in the ORIGINAL full-envelope interior. All finiteness, Noetherianity and
fullness inputs are constructed from the proper family. No coefficient class
extension, finite ambient translation, or open generic fiber is assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [Algebra.FiniteType ℤ R]
  [IrreducibleSpace (Spec (.of R))] [Field K] [IsAlgClosed K]
  {X : Scheme} (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f]
  [GeometricallyIntegral f] [SmoothOfRelativeDimension 1 f]
  {L : X.Modules} (hL : AmpleLineBundle L)
  (t : Spec (.of K) ⟶ Spec (.of R))
local notation "η" => (default : Spec (CommRingCat.of K))

include hL in
/-- Arbitrary generic-fiber classes have actual full-interior parameters over the original base. -/
theorem exists_arbitrary_geometric_generic_interior
    (ht : t η = genericPoint (Spec (.of R)))
    (s : (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : (relativeFppfSheaf f).obj.obj (op V))
      (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
      (b : Over.mk t ⟶ A), IsAffine V.left ∧ Etale V.hom ∧ IsAffine A.left ∧
      ∃ hk : IsOpenImmersion k.left, let _ := hk
      (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V c k) = s ∧
      b.left η ∈ fullEnvelopeInterior f hL d V c k := by
  obtain ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, hx⟩ :=
    exists_arbitrary_geometric_affine_full_fiber f hL t s
  let _ := hV
  let _ := he
  let _ := hA
  let _ := hk
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := EnvelopeVerticalGenerizations.original_envelope_noetherian A V
  refine ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, ?_⟩
  apply EnvelopeVerticalGenerizations.interior_over_generic_coefficient A V
    (toEnvelope f hL d V c k).left.opensRange (b.left η) hx
  exact (congrArg (fun g : Spec (.of K) ⟶ Spec (.of R) ↦ g η) b.w).trans ht

end FLT.Mazur.HilbertChart.AffineRestriction
