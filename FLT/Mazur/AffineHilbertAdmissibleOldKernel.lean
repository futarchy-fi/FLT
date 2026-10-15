/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertPrincipalFiniteKernel

/-!
# Admissible principal certificates in the original finite coefficient model

An actual admissible invariant coefficient constructs the full original
Picard kernel for the OLD coefficient map on its principal source. The
inverse is an actual scheme morphism retaining both original endpoints.
Neither representatives nor a full-envelope hypothesis are input. This
certifies this source open, without asserting that it covers all classes.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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
  (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
  (hs : s ∈ invariantEnvelopeDenominators f hL d V c k)
local notation "u" => invariantPrincipalSourceMap f hL d V c k s
local notation "l" => invariantPrincipalChart f hL d V c k s
local notation "w" => Over.Hom.left (u ≫ finiteKernelProjection f hL d V c k)
local notation "p" => Over.Hom.left (fst f hL d V c l)
local notation "q" => Over.Hom.left (snd f hL d V c l)
local notation "h" => congrArg Over.Hom.left (principalOldFinite_condition f hL d V c k s)
local notation "m" => pullback.lift p q h

include hs in
/-- Admissibility reconstructs the entire restricted kernel of the unchanged OLD finite model. -/
theorem admissibleOldFinite_isPullback : IsPullback p q w w :=
  principalOldFinite_isPullback f hL d V c k s (admissibleFinite_isPullback f hL d V c k s hs)

/-- An actual original Picard arrow for every test in the old restricted finite kernel. -/
def admissibleOldFiniteKernelInverse : pullback w w ⟶ (relation f hL d V c l).left :=
  (admissibleOldFinite_isPullback f hL d V c k s hs).lift
    (pullback.fst w w) (pullback.snd w w) pullback.condition

/-- The inverse retains the first original source coordinate. -/
@[reassoc]
theorem admissibleOldFiniteKernelInverse_fst :
    admissibleOldFiniteKernelInverse f hL d V c k s hs ≫ p = pullback.fst w w :=
  (admissibleOldFinite_isPullback f hL d V c k s hs).lift_fst _ _ _

/-- The second original source coordinate is independent and also retained. -/
@[reassoc]
theorem admissibleOldFiniteKernelInverse_snd :
    admissibleOldFiniteKernelInverse f hL d V c k s hs ≫ q = pullback.snd w w :=
  (admissibleOldFinite_isPullback f hL d V c k s hs).lift_snd _ _ _

/-- The certificate is an inverse on the entire scheme, including all nilpotent directions. -/
@[reassoc]
theorem admissibleOldFiniteKernelInverse_comp :
    admissibleOldFiniteKernelInverse f hL d V c k s hs ≫ m = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, admissibleOldFiniteKernelInverse_fst,
      Category.id_comp]
  · rw [Category.assoc, pullback.lift_snd, admissibleOldFiniteKernelInverse_snd,
      Category.id_comp]

include hs in
/-- All residue-field branches of the old restricted kernel have actual original preimages. -/
theorem admissibleOldFiniteKernel_image (z : (pullback w w : Scheme)) : z ∈ Set.range m :=
  ⟨admissibleOldFiniteKernelInverse f hL d V c k s hs z,
    congrArg (fun t ↦ t z) (admissibleOldFiniteKernelInverse_comp f hL d V c k s hs)⟩

end FLT.Mazur.HilbertChart.AffineRestriction
