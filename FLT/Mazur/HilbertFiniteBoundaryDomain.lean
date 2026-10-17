/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteTargetSaturation
public import FLT.Mazur.HilbertBoundaryRelationTests

/-!
# The full original boundary over the saturated finite target locus

The original closed source inherits a constructed invariant open from the
ambient finite locus. Its whole original first relation projection is finite
there. No claim that this open covers all boundary points is made.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeOpenEnvelope
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "i" => Over.Hom.left (originalBoundarySourceMap f hL d V c k)
local notation "r" => Over.Hom.left (originalClosedFst f hL d V c k)
local notation "s" => Over.Hom.left (originalClosedSnd f hL d V c k)
local notation "z" => Over.Hom.left (originalClosedArrow f hL d V c k)
attribute [local irreducible] relation fst snd originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow

/-- The actual open of the original boundary lying over the ambient finite target locus. -/
def originalBoundaryFiniteDomain : (originalBoundarySource f hL d V c k).left.Opens :=
  i ⁻¹ᵁ finiteTargetOpen p

/-- This boundary domain retains all arrows at both independent original endpoints. -/
theorem originalBoundaryFiniteDomain_invariant :
    r ⁻¹ᵁ originalBoundaryFiniteDomain f hL d V c k =
      s ⁻¹ᵁ originalBoundaryFiniteDomain f hL d V c k := by
  have hp := congrArg Over.Hom.left (originalClosedArrow_fst f hL d V c k)
  have hq := congrArg Over.Hom.left (originalClosedArrow_snd f hL d V c k)
  simp only [Over.comp_left] at hp hq
  unfold originalBoundaryFiniteDomain
  rw [← Scheme.Hom.comp_preimage, ← hp, Scheme.Hom.comp_preimage,
    originalFiniteTarget_preimage_eq f hL d V c k,
    ← Scheme.Hom.comp_preimage, hq, Scheme.Hom.comp_preimage]

omit [IsAffine V.left] [Etale V.hom] [IsAffine A.left] in
/-- The whole boundary projection is finite over this constructed invariant domain. -/
theorem originalBoundaryFiniteDomain_finite :
    IsFinite (r ∣_ originalBoundaryFiniteDomain f hL d V c k) := by
  let _ := finite_restrict_finiteTarget p
  exact finite_restrict_of_isPullback (originalClosedFst_isPullback f hL d V c k)
    (finiteTargetOpen p)

omit [IsAffine V.left] [Etale V.hom] [IsAffine A.left] in
/-- Every point of the constructed boundary domain has an actual finite target neighborhood. -/
theorem originalBoundaryFiniteDomain_le :
    originalBoundaryFiniteDomain f hL d V c k ≤ finiteTargetOpen r :=
  preimage_finiteTargetOpen_le (originalClosedFst_isPullback f hL d V c k)

end FLT.Mazur.HilbertChart.AffineRestriction
