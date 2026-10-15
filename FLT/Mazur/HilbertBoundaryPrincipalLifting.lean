/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryPrincipalLocalization
public import FLT.Mazur.RelativeRelationPrincipalLifting

/-!
# The original boundary local lifting criterion

On the constructed principal neighborhoods, local lifting is exactly
finite-power vanishing of the original full-relation obstruction. This
criterion retains the unchanged coefficient base and both original endpoints.
Its finite-power vanishing still requires the remaining geometric argument.
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


/-- The original closed comparison in the explicit invariant section rings. -/
def originalClosedSectionPullback : (invariantSheaf e).obj.obj (op W) →+*
    (invariantSheaf ec).obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj W)) :=
  invariantSectionPullback e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W

local notation "j" => homOfLE (invariantPrincipal_le e W v)

include hW in
/-- Local original boundary lifts are equivalent to lifts of a finite power multiple. -/
theorem originalClosed_principal_lift_iff
    (t : (invariantSheaf ec).obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj W))) :
    (∃ a : (invariantSheaf e).obj.obj (op N), (m).c.app (op N) a =
      (invariantSheaf ec).obj.map ((TopologicalSpace.Opens.map (m).base).map j).op t) ↔
    ∃ (n : ℕ) (a : (invariantSheaf e).obj.obj (op W)),
      (m).c.app (op W) a = originalClosedSectionPullback f hL d V c k W v ^ n * t :=
  invariantMap_principal_lift_iff e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W hW
    ((p).left.isCompact_preimage hW.isCompact) v t

/-- The principal obstruction vanishes exactly when an original power obstruction vanishes. -/
theorem originalPrincipalClosedObstruction_restrict_eq_zero_iff
    (t : (invariantSheaf ec).obj.obj (op ((TopologicalSpace.Opens.map (m).base).obj W))) :
    originalPrincipalClosedObstruction f hL d V c k W hW v
      ((invariantSheaf ec).obj.map ((TopologicalSpace.Opens.map (m).base).map j).op t) = 0 ↔
    ∃ n : ℕ, originalClosedSectionObstruction f hL d V c k W hW
      (originalClosedSectionPullback f hL d V c k W v ^ n * t) = 0 := by
  rw [originalPrincipalClosedObstruction_eq_zero_iff,
    originalClosed_principal_lift_iff f hL d V c k W hW v]
  exact exists_congr fun n ↦
    (originalClosedSectionObstruction_eq_zero_iff f hL d V c k W hW _).symm

end FLT.Mazur.HilbertChart.AffineRestriction
