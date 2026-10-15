/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ArbitraryGeometricAffineFullFiber
public import FLT.Mazur.ArtinianGroundEnvelopeInterior
public import FLT.Mazur.AffineHilbertFullFiberInterior

/-!
# Original full interiors reached from an Artinian etale neighborhood

The original coefficient scheme need not be Artinian. If the geometric
coefficient map lifts to an actual locally Artinian etale neighborhood, its
constructed ORIGINAL full fiber is interior. The whole original parameter
map and class remain unchanged; no changed-family finite branch replaces the
original independent translation. Existence of such a neighborhood is not
asserted for arbitrary coefficient points.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  {U : Scheme} (q : U ⟶ Spec (.of R)) [IsLocallyArtinian U] [Etale q]

/-- Reaching the original coefficient point from Artinian etale ground removes its obstruction. -/
theorem fullEnvelopeInterior_of_artinian_ground (d : ℕ) (V : Over (Spec (.of R)))
    [Etale V.hom] [QuasiCompact V.hom]
    (c : (relativeFppfSheaf f).obj.obj (op V))
    {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)
    [IsOpenImmersion k.left] (x : A.left)
    (hx : x ∈ fullEnvelopeLocus f hL d V c k) (u : U) (hu : A.hom x = q u) :
    x ∈ fullEnvelopeInterior f hL d V c k := by
  obtain ⟨y, hy, _⟩ := Scheme.exists_preimage_of_isPullback
    (IsPullback.of_hasPullback A.hom q) x u hu
  have hi := ArtinianGroundEnvelope.original_interior_of_open_comparison A V q
    (toEnvelope f hL d V c k).left.opensRange (pullback.fst A.hom q).isOpenMap y
    (by simpa only [hy, fullEnvelopeLocus] using hx)
  change pullback.fst A.hom q y ∈ fullEnvelopeInterior f hL d V c k at hi
  rwa [hy] at hi

variable {K : Type} [Field K] [IsAlgClosed K]
  (t : Spec (.of K) ⟶ Spec (.of R)) (z : Spec (.of K) ⟶ U) (hz : z ≫ q = t)
local notation "η" => (default : Spec (CommRingCat.of K))

include hL hz in
/-- An arbitrary class reached by this neighborhood has an original full-interior parameter. -/
theorem exists_arbitrary_geometric_artinian_ground_interior
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
  let _ := hk
  refine ⟨d, V, c, A, k, b, hV, he, hA, hk, hb, ?_⟩
  apply fullEnvelopeInterior_of_artinian_ground f hL q d V c k (b.left η) hx (z η)
  exact congrArg (fun g : Spec (.of K) ⟶ Spec (.of R) ↦ g η) (b.w.trans hz.symm)

end FLT.Mazur.HilbertChart.AffineRestriction
