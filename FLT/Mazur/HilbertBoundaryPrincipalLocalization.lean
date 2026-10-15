/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryQuotientSections
public import FLT.Mazur.AffineHilbertBoundedRelation
public import FLT.Mazur.RelativeRelationInvariantLocalization

/-!
# Original boundary principal neighborhoods and invariant localization

These are actual opens of the original orbit space with affine source domains.
Full relation compactness is supplied by the original proper-family geometry,
for every original etale translation. Localization is proved for the actual
invariant sheaf, without asserting that the quotient opens are affine schemes.
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
local notation "B" => originalBoundarySource f hL d V c k
local notation "i" => originalBoundarySourceMap f hL d V c k
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k

local notation "C" => originalClosedRelation f hL d V c k
local notation "r" => originalClosedFst f hL d V c k
local notation "s" => originalClosedSnd f hL d V c k
local notation "z" => originalClosedArrow f hL d V c k

open RelativeRelationOrbit
local notation "e" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence relation fst snd equivalence

local notation "m" => originalClosedInvariantMap f hL d V c k

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
  (hW : IsAffineOpen (pullOpen (equivalence f hL d V c k) W).val)
  (v : (invariantSheaf (equivalence f hL d V c k)).obj.obj (op W))
local notation "N" => invariantPrincipal e W v

omit [Etale V.hom] [IsAffine A.left] [IsOpenImmersion k.left] in
include hW in
/-- Every original principal neighborhood has an affine original source domain. -/
theorem originalPrincipal_source_affine : IsAffineOpen (pullOpen e N).val :=
  invariantPrincipal_source_affine e W hW v

/-- The closed boundary pulls this neighborhood back to the actual restricted unit locus. -/
theorem originalClosed_principal :
    (TopologicalSpace.Opens.map (m).base).obj N =
      invariantPrincipal ec ((TopologicalSpace.Opens.map (m).base).obj W)
        ((m).c.app (op W) v) :=
  LocallyRingedSpace.preimage_basicOpen m v

include hW in
/-- The full original closed source over each of these neighborhoods is affine. -/
theorem originalClosed_principal_source_affine :
    IsAffineOpen (pullOpen ec ((TopologicalSpace.Opens.map (m).base).obj N)).val :=
  invariantMap_principal_source_affine e W v ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) hW

include hW in
/-- Original full invariant functions localize on every such neighborhood. -/
theorem originalPrincipal_isLocalization :
    @IsLocalization.Away _ _ v ((invariantSheaf e).obj.obj (op N)) _
      (principalRestriction e W v).toAlgebra := by
  apply principalRestriction_isLocalization e W v hW
  exact (p).left.isCompact_preimage hW.isCompact

include hW in
/-- Local original invariant sections have actual original invariant numerators. -/
theorem originalPrincipal_invariant_numerator (b : (invariantSheaf e).obj.obj (op N)) :
    ∃ (n : ℕ) (a : (invariantSheaf e).obj.obj (op W)),
      b * principalRestriction e W v v ^ n = principalRestriction e W v a :=
  principalRestriction_invariant_numerator e W v hW
    ((p).left.isCompact_preimage hW.isCompact) b

/-- The boundary lifting obstruction is defined on every constructed principal neighborhood. -/
def originalPrincipalClosedObstruction :
    (invariantSheaf ec).obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj N)) →+
      originalClosedSectionObstructionGroup f hL d V c k N :=
  originalClosedSectionObstruction f hL d V c k N
    (originalPrincipal_source_affine f hL d V c k W hW v)

/-- Local obstruction vanishing means a lift on the actual original principal neighborhood. -/
theorem originalPrincipalClosedObstruction_eq_zero_iff
    (b : (invariantSheaf ec).obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj N))) :
    originalPrincipalClosedObstruction f hL d V c k W hW v b = 0 ↔
      ∃ a : (invariantSheaf e).obj.obj (op N), (m).c.app (op N) a = b :=
  originalClosedSectionObstruction_eq_zero_iff f hL d V c k N
    (originalPrincipal_source_affine f hL d V c k W hW v) b

end FLT.Mazur.HilbertChart.AffineRestriction
