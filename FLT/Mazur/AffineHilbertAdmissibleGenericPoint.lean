/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteFiberInvariants
public import FLT.Mazur.AffineHilbertAdmissibleGenericCoefficients

/-!
# One admissible original point covers every generic finite-model branch

Full kernel saturation propagates the same coefficient through the entire
generic source fiber. The old finite-model inverse neighborhoods and their
nonnilpotent target coefficient are then constructed. The input is one actual
nonvanishing admissible source coefficient, not a chosen original relation arrow.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "v" => finiteKernelProjection f hL d V c k
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k)
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
local notation "K" => (pullback (Over.Hom.left v) (Over.Hom.left v) : Scheme)
local notation "T" => (Over.left (finiteKernelModel f hL d V c k) : Scheme)
local notation "D" => (Over.left (relation f hL d V c k) : Scheme)
variable [IrreducibleSpace (finiteKernelModel f hL d V c k).left]
  (x : A.left)
  (hx : (finiteKernelProjection f hL d V c k).left x =
    genericPoint (finiteKernelModel f hL d V c k).left)
  (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
  (hs : s ∈ invariantEnvelopeDenominators f hL d V c k)
  (hxs : x ∈ A.left.basicOpen s.val)

omit [IsAffine V.left] in
include hx hs hxs in
/-- A single coefficient at one generic-fiber point covers every branch of that source fiber. -/
theorem generic_admissible_source_coverage :
    ∀ y : A.left, (v).left y = genericPoint T →
      ∃ t : compatibleFunctions p q,
        t ∈ invariantEnvelopeDenominators f hL d V c k ∧
          y ∈ A.left.basicOpen t.val := by
  intro y hy
  exact finiteFiber_admissible_coverage f hL d V c k x s hs hxs y (hy.trans hx.symm)

include hx hs hxs in
/-- The original finite target has a nonempty effective open, constructed from one source point. -/
theorem finiteModelEffectiveTarget_nonempty_of_admissible_point :
    Nonempty (modelEffectiveTarget f hL d V c k v h).left :=
  finiteModelEffectiveTarget_nonempty_of_admissible_coverage f hL d V c k
    (generic_admissible_source_coverage f hL d V c k x hx s hs hxs)

include hx hs hxs in
/-- All actual old kernel inverse charts and a nonnilpotent old target coefficient are obtained. -/
theorem finiteModel_coefficient_of_admissible_point :
    ∃ (t : Finset Γ(K, ⊤)) (r : Γ(T, ⊤)),
      (∀ a ∈ t, ∃ b : ((K).basicOpen a).toScheme ⟶ D,
        b ≫ pullback.lift p q h = ((K).basicOpen a).ι) ∧
      (pullback.fst (v).left (v).left ≫ (v).left).appTop r ∈
        Ideal.span (t : Set Γ(K, ⊤)) ∧ ¬ IsNilpotent r :=
  finiteModel_coefficient_of_admissible_coverage f hL d V c k
    (generic_admissible_source_coverage f hL d V c k x hx s hs hxs)

include hx hs hxs in
/-- An integral original source gives a represented original Picard fppf region. -/
theorem finiteModelPicardFppfTarget_nonempty_of_admissible_point [IsIntegral A.left] :
    Nonempty (finiteModelPicardFppfTarget f hL d V c k).left :=
  finiteModelPicardFppfTarget_nonempty_of_admissible_coverage f hL d V c k
    (generic_admissible_source_coverage f hL d V c k x hx s hs hxs)

end FLT.Mazur.HilbertChart.AffineRestriction
