/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertBoundaryThickeningQuotients
public import FLT.Mazur.HilbertBoundaryThickeningNilpotence
public import FLT.Mazur.RelativeRelationNilpotentSections

/-!
# Nilpotent structure-sheaf kernels on the original quotient tower

The actual quotient transition, expressed in invariant coordinates, has a
nilpotent kernel on every open with affine source inverse image. In particular
this holds on global sections, with the explicit exponent `n + 1`. The result
uses the full original relation and does not assume quotient scheme effectivity
or surjectivity of the quotient structure-sheaf maps.
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
local notation "I" => boundaryIdealSheaf π O
local notation "B" n:max => originalThickenedSource f hL d V c k n
local notation "i" n:max => originalThickenedSourceMap f hL d V c k n
local notation "C" n:max => originalThickenedRelation f hL d V c k n
local notation "r" n:max => originalThickenedFst f hL d V c k n
local notation "s" n:max => originalThickenedSnd f hL d V c k n
local notation "z" n:max => originalThickenedArrow f hL d V c k n

open RelativeRelationOrbit
local notation "Q" n:max => locallyRingedQuotient (p := r n) (q := s n)
local notation "P" n:max => locallyRingedProjection (p := r n) (q := s n)
local notation "Q₀" => locallyRingedQuotient
  (p := fst f hL d V c k) (q := snd f hL d V c k)
local notation "P₀" => locallyRingedProjection
  (p := fst f hL d V c k) (q := snd f hL d V c k)

attribute [local irreducible] originalThickenedSource originalThickenedSourceMap
  originalThickenedRelation originalThickenedFst originalThickenedSnd originalThickenedArrow

local notation "e" n:max => originalThickenedEquivalence f hL d V c k n

variable {m n : ℕ} (h : m ≤ n)

/-- The original tower transition in invariant structure-sheaf coordinates. -/
def originalThickenedInvariantTransition :
    invariantLocallyRingedSpace (e m) ⟶ invariantLocallyRingedSpace (e n) :=
  invariantMap (e n) (e m) (originalThickenedTransition f hL d V c k h).left
    (originalThickenedRelationTransition f hL d V c k h).left
    (congrArg Over.Hom.left (originalThickenedRelationTransition_fst f hL d V c k h))
    (congrArg Over.Hom.left (originalThickenedRelationTransition_snd f hL d V c k h))

local notation "t" => originalThickenedInvariantTransition f hL d V c k h

/-- This is the whole previously constructed quotient transition, including its sheaf map. -/
@[reassoc]
theorem originalThickenedInvariantTransition_comparison :
    (invariantLocallyRingedIso (e m)).hom ≫ t =
      originalThickenedQuotientTransition f hL d V c k h ≫
        (invariantLocallyRingedIso (e n)).hom := by
  let _ : Epi (P m) := by
    dsimp only [locallyRingedProjection]
    infer_instance
  apply (cancel_epi (P m)).mp
  rw [← Category.assoc]
  change invariantLocallyRingedProjection (e m) ≫ t = _
  rw [originalThickenedQuotientTransition_projection_assoc]
  exact invariantMap_projection (e n) (e m)
    (originalThickenedTransition f hL d V c k h).left
    (originalThickenedRelationTransition f hL d V c k h).left _ _

/-- The section kernel is annihilated by the target-order exponent, on each affine source domain. -/
theorem originalThickenedInvariantTransition_ker_pow
    (W : TopologicalSpace.Opens (Orbit (e n))) (hW : IsAffineOpen (pullOpen (e n) W).val) :
    RingHom.ker ((t).c.app (op W)).hom ^ (n + 1) = ⊥ :=
  invariantMap_section_ker_pow (e n) (e m)
    (originalThickenedTransition f hL d V c k h).left
    (originalThickenedRelationTransition f hL d V c k h).left _ _ W hW (n + 1)
    (originalThickenedTransition_ker_pow f hL d V c k h)

/-- The entire infinitesimal source is affine, so the global comparison has this exact bound. -/
theorem originalThickenedInvariantTransition_top_ker_pow :
    RingHom.ker ((t).c.app (op ⊤)).hom ^ (n + 1) = ⊥ := by
  apply originalThickenedInvariantTransition_ker_pow
  have he : (pullOpen (e n) ⊤).val = ⊤ := by ext x; rfl
  rw [he]
  exact isAffineOpen_top (B n).left

/-- A whole invariant function lost at a lower order is nilpotent with the same bound. -/
theorem originalThickenedInvariantTransition_pow_eq_zero
    (W : TopologicalSpace.Opens (Orbit (e n))) (hW : IsAffineOpen (pullOpen (e n) W).val)
    (a : (invariantSheaf (e n)).obj.obj (op W)) (ha : (t).c.app (op W) a = 0) :
    a ^ (n + 1) = 0 :=
  invariantMap_section_pow_eq_zero (e n) (e m)
    (originalThickenedTransition f hL d V c k h).left
    (originalThickenedRelationTransition f hL d V c k h).left _ _ W hW (n + 1)
    (originalThickenedTransition_ker_pow f hL d V c k h) a ha

end FLT.Mazur.HilbertChart.AffineRestriction
