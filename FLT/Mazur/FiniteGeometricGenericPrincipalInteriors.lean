/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricAffineFullFiber
public import FLT.Mazur.DenseGroundHilbertPrincipal

/-!
# Finite families of generic-fiber classes retain principal affine interiors

One original affine etale translation and one degree work for every member
of a finite family of arbitrary generic-fiber Picard classes. The constructed
dense coefficient open contains their generic coefficient point. Each class
then has an original affine principal parameter in the full interior of its
OWN restricted chart, with exact original Hilbert and class recovery.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve AffineEtaleDenseFiniteGround
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R K : Type} [CommRing R] [IsDomain R] [Algebra.FiniteType ℤ R]
  [Field K] [IsAlgClosed K] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (t : Spec (.of K) ⟶ Spec (.of R))
local notation "η" => (default : Spec (CommRingCat.of K))

include hL in
/-- One degree and translation retain every prescribed generic class through affine interiors. -/
theorem exists_finite_geometric_generic_principal_interiors {n : ℕ}
    (ht : t η = genericPoint (Spec (.of R)))
    (s : Fin n → (relativeFppfSheaf f).obj.obj (op (Over.mk t))) :
    ∃ (d : ℕ) (V : Over (Spec (.of R)))
      (c : Fin n → (relativeFppfSheaf f).obj.obj (op V)),
      ∃ hV : IsAffine V.left, ∃ he : Etale V.hom, let _ := hV; let _ := he
      t η ∈ groundOpen R V ∧ ∀ i,
      ∃ (A : Over (Spec (.of R))) (k : A ⟶ variableHilbertTest f d V)
        (b : Over.mk t ⟶ A), IsAffine A.left ∧
        ∃ hk : IsOpenImmersion k.left, let _ := hk
        (relativeFppfSheaf f).obj.map b.op (sectionAt f hL d V (c i) k) = s i ∧
        ∃ (r : Γ(A.left, ⊤)) (b' : Over.mk t ⟶ orbitPrincipalSource r),
          A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V (c i) k ∧
          b' ≫ orbitPrincipalSourceMap r = b ∧
          b' ≫ orbitPrincipalChart f d V k r = b ≫ k ∧
          (relativeFppfSheaf f).obj.map b'.op
            (sectionAt f hL d V (c i) (orbitPrincipalChart f d V k r)) = s i ∧
          b'.left η ∈ fullEnvelopeInterior f hL d V (c i) (orbitPrincipalChart f d V k r) := by
  obtain ⟨d, V, c, hV, he, h⟩ := exists_finite_geometric_affine_full_fibers f hL t s
  let _ := hV
  let _ := he
  have ht' : t η ∈ groundOpen R V := by
    rw [ht]
    obtain ⟨x, hx⟩ := (groundOpen_dense R V).nonempty
    exact (genericPoint_specializes x).mem_open (groundOpen R V).isOpen hx
  refine ⟨d, V, c, hV, he, ht', fun i ↦ ?_⟩
  obtain ⟨A, k, b, hA, hk, hb, hx⟩ := h i
  let _ := hA
  let _ := hk
  obtain ⟨r, b', hr, hc, hp, hs, hi⟩ :=
    exists_denseGround_geometric_principal f hL d V (c i) k b hx ht'
  exact ⟨A, k, b, hA, hk, hb, r, b', hr, hc, hp, hs.trans hb, hi⟩

end FLT.Mazur.HilbertChart.AffineRestriction
