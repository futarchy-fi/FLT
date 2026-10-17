/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertDerivedNoetherianRelation
public import FLT.Mazur.EquivalenceRelationCompleteInteriorFinite
public import FLT.Mazur.HilbertFullRelationFiberRebase
public import FLT.Mazur.AffineHilbertSymmetricNeighborhoods
public import FLT.Mazur.HilbertFiniteTargetSaturation

/-!
# The exact scope of complete interior charts in the original Hilbert relation

A complete interior lift exists exactly at points of the original finite
locus. Thus constructing more such lifts cannot bypass that locus. Complete
closed and infinitesimal tests remain available outside it.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve RelativeRelationOrbit SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "e" => equivalence f hL d V c k
attribute [local irreducible] relation fst snd equivalence

open EquivalenceRelationNormalizedFrames

/-- Complete interior lifts detect actual finite neighborhoods of the original relation. -/
theorem originalFiniteTarget_iff_completeInterior (x : A.left) :
    x ∈ finiteTargetOpen (p).left ↔
      ∃ (n : ℕ) (o : Fin n) (y : source (p).left (q).left (Fin n) o),
        first (p).left (q).left (Fin n) o y = x ∧
          y ∈ completeInterior (Fin n) o := by
  let _ : LocallyQuasiFinite (p).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
  exact finiteTarget_iff_exists_completeInterior (fullRelationSchemeEquivalence f hL d V c k) x

/-- The original finite orbit open is precisely the image of all complete interior frames. -/
theorem originalFiniteOrbit_iff_completeInterior (x : A.left) :
    projection e x ∈ originalFiniteOrbitOpen f hL d V c k ↔
      ∃ (n : ℕ) (o : Fin n) (y : source (p).left (q).left (Fin n) o),
        first (p).left (q).left (Fin n) o y = x ∧
          y ∈ completeInterior (Fin n) o := by
  rw [mem_originalFiniteOrbitOpen_iff, originalFiniteTarget_iff_completeInterior]

/-- Outside the original finite locus no complete lift can avoid the incomplete-frame closure. -/
theorem originalCompleteLift_not_interior (x : A.left)
    (hx : x ∉ finiteTargetOpen (p).left) (n : ℕ) (o : Fin n)
    (y : source (p).left (q).left (Fin n) o)
    (hy : first (p).left (q).left (Fin n) o y = x) :
    y ∉ completeInterior («p» := (p).left) («q» := (q).left) (Fin n) o := by
  intro hc
  exact hx ((originalFiniteTarget_iff_completeInterior f hL d V c k x).mpr ⟨n, o, y, hy, hc⟩)

end FLT.Mazur.HilbertChart.AffineRestriction
