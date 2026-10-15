/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.SchemeRelationPrincipalKernelTests
public import FLT.Mazur.AffineHilbertPrincipalInvariants
public import FLT.Mazur.AffineHilbertNestedKernel
public import FLT.Mazur.AffineHilbertAdmissibleFiniteKernel

/-!
# Old and recomputed finite kernel tests on original principal charts

On any invariant principal source, equality in the old finite coefficient
model is equivalent to equality in the newly computed model. The comparison
uses full invariant localization and the original double relation. It retains
arbitrary nonreduced tests and makes no identification of the finite targets.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom] [IsAffine V.left]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
variable (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
local notation "B" => invariantPrincipalSource f hL d V c k s
local notation "u" => invariantPrincipalSourceMap f hL d V c k s
local notation "l" => invariantPrincipalChart f hL d V c k s
local notation "v₀" => finiteKernelProjection f hL d V c k
local notation "v₁" => finiteKernelProjection f hL d V c l

/-- Full original invariant tests survive recomputation of the actual principal chart relation. -/
theorem principalInvariant_test_iff {T : Over (Spec (.of R))} (a b : T ⟶ B) :
    a ≫ invariantAffineProjection f hL d V c l =
        b ≫ invariantAffineProjection f hL d V c l ↔
      (a ≫ u) ≫ invariantAffineProjection f hL d V c k =
        (b ≫ u) ≫ invariantAffineProjection f hL d V c k := by
  unfold invariantPrincipalChart
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := relation_compactSpace f hL d V c k
  let _ := relation_quasiSeparatedSpace f hL d V c k
  have h := SchemeRelationPrincipalLocalization.recomputed_projection_test_iff
    (p).left (q).left s (fst f hL d V c (u ≫ k)).left
    (snd f hL d V c (u ≫ k)).left (nestedSchemeDoubleIso f hL d V c k u)
    (nestedSchemeDoubleIso_fst f hL d V c k u)
    (nestedSchemeDoubleIso_snd f hL d V c k u) a.left b.left
  constructor
  · intro hab
    apply Over.OverMorphism.ext
    apply h.mp
    exact congrArg Over.Hom.left hab
  · intro hab
    apply Over.OverMorphism.ext
    apply h.mpr
    exact congrArg Over.Hom.left hab

/-- The exact old finite coefficients and freshly computed coefficients have the same tests. -/
theorem principalFinite_test_iff {T : Over (Spec (.of R))} (a b : T ⟶ B) :
    a ≫ v₁ = b ≫ v₁ ↔ (a ≫ u) ≫ v₀ = (b ≫ u) ≫ v₀ := by
  rw [finiteKernelProjection_test_iff, finiteKernelProjection_test_iff]
  exact principalInvariant_test_iff f hL d V c k s a b

end FLT.Mazur.HilbertChart.AffineRestriction
