/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationPairedAffineCover
public import FLT.Mazur.HilbertNormalizedStableAffine
public import FLT.Mazur.RelativeRankPullbackThickenings

/-!
# Actual paired affine lifts for the full Hilbert relation

The original Hilbert affine envelope supplies the common chart construction.
On an unsplit rank thickening the first exact rank hypothesis is automatic.
The independent second endpoint must still be shown to have that rank; no
original arrow or equality of all invariants is presumed or inferred here.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames RelativeOrderedTuples
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
  (n : ℕ) (o : Fin n)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "N" => normalizedFullRelationFrames f hL d V c k n o
local notation "ρ" => normalizedFullRelationAction f hL d V c k n o
local notation "π" => normalizedFullRelationFirst f hL d V c k n o

local instance hilbertPairOver_etale : Etale (Over.mk p).hom := inferInstanceAs (Etale p)
local instance hilbertPairOver_separated : IsSeparated (Over.mk p).hom :=
  inferInstanceAs (IsSeparated p)
local instance hilbertPairOver_compact : QuasiCompact (Over.mk p).hom :=
  inferInstanceAs (QuasiCompact p)

/-- The original envelope constructs common affine charts for every pair of equal-rank tests. -/
theorem exists_paired_normalized_affine_lifts {B : Scheme.{0}} (x y : B ⟶ A.left)
    (hx : Set.range x ⊆ exactRank (Over.mk p) n)
    (hy : Set.range y ⊆ exactRank (Over.mk p) n) (z : B) :
    ∃ (U : (N).Opens) (T : Scheme.{0}) (a b : T ⟶ U.toScheme)
      (v : T ⟶ B) (t : T),
      IsAffineOpen U ∧ IsAffine T ∧ Etale v ∧ v t = z ∧
      (∀ g : Equiv.Perm (Fin n), (ρ g).hom ⁻¹ᵁ U = U) ∧
      a ≫ U.ι ≫ π = v ≫ x ∧ b ≫ U.ι ≫ π = v ≫ y := by
  let _ := finTuples_affine (firstRelationEnvelope (A := A) V) n
  exact exists_paired_affine_endpoint_lifts (fullRelationSchemeEquivalence f hL d V c k)
    n o (normalizedOriginalFrameInclusion f hL d V c k n o)
    (fullRelationOrderedEnvelopeMap f hL d V c k n) x y hx hy z

/-- Full rank stages have common affine lifts when the second rank matches. -/
theorem exists_rankStage_paired_normalized_affine_lifts {B : Scheme.{0}}
    (x y : B ⟶ A.left) (r : ℕ)
    (hy : Set.range (rankPullbackMap (Over.mk p) x n r ≫ y) ⊆ exactRank (Over.mk p) n)
    (z : rankPullbackThickening (Over.mk p) x n r) :
    ∃ (U : (N).Opens) (T : Scheme.{0}) (a b : T ⟶ U.toScheme)
      (v : T ⟶ rankPullbackThickening (Over.mk p) x n r) (t : T),
      IsAffineOpen U ∧ IsAffine T ∧ Etale v ∧ v t = z ∧
      (∀ g : Equiv.Perm (Fin n), (ρ g).hom ⁻¹ᵁ U = U) ∧
      a ≫ U.ι ≫ π = v ≫ rankPullbackMap (Over.mk p) x n r ≫ x ∧
      b ≫ U.ι ≫ π = v ≫ rankPullbackMap (Over.mk p) x n r ≫ y := by
  apply exists_paired_normalized_affine_lifts f hL d V c k n o _ _ _ hy z
  rintro _ ⟨w, rfl⟩
  exact rankPullback_endpoint (Over.mk p) x n r w

end FLT.Mazur.HilbertChart.AffineRestriction
