/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.EquivalenceRelationFiniteTargetSaturation
public import FLT.Mazur.HilbertFullRelationFiberRebase
public import FLT.Mazur.AffineHilbertSymmetricNeighborhoods
public import FLT.Mazur.RelativeRelationOrbitOpens

/-!
# The exact finite locus of the original Hilbert relation descends to its orbit space

Intrinsic étaleness and the actual affine envelope prove that the finite
locus is invariant. It therefore gives an original orbit open, with precisely
the original finite locus as its source. Global finiteness is not assumed.
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

/-- The original finite target locus is invariant under all original Hilbert relation arrows. -/
theorem originalFiniteTarget_preimage_eq :
    (p).left ⁻¹ᵁ finiteTargetOpen (p).left =
      (q).left ⁻¹ᵁ finiteTargetOpen (p).left := by
  let _ : LocallyQuasiFinite (p).left :=
    LocallyQuasiFinite.of_finite_preimage_singleton _ (fst_finite_fiber f hL d V c k)
  exact EquivalenceRelationFiber.finiteTargetOpen_preimage_eq
    (fullRelationSchemeEquivalence f hL d V c k)

/-- The intrinsic finite target locus as an actual invariant domain. -/
def originalFiniteInvariantOpen : InvariantOpens p q :=
  ⟨finiteTargetOpen (p).left, originalFiniteTarget_preimage_eq f hL d V c k⟩

/-- The corresponding actual open of the original orbit space. -/
def originalFiniteOrbitOpen : TopologicalSpace.Opens (Orbit e) :=
  descendOpen e (originalFiniteInvariantOpen f hL d V c k)

/-- Pulling back the constructed quotient domain recovers exactly the original finite locus. -/
theorem pullOpen_originalFiniteOrbitOpen :
    (pullOpen e (originalFiniteOrbitOpen f hL d V c k)).val = finiteTargetOpen (p).left :=
  congrArg Subtype.val (pullOpen_descendOpen e (originalFiniteInvariantOpen f hL d V c k))

/-- Membership in the orbit open is tested at any original source representative. -/
theorem mem_originalFiniteOrbitOpen_iff (x : A.left) :
    projection e x ∈ originalFiniteOrbitOpen f hL d V c k ↔
      x ∈ finiteTargetOpen (p).left := by
  change x ∈ (pullOpen e (originalFiniteOrbitOpen f hL d V c k)).val ↔ _
  rw [pullOpen_originalFiniteOrbitOpen]

end FLT.Mazur.HilbertChart.AffineRestriction
