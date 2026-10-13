/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertInvariantRegularNorm
public import FLT.Mazur.AffineHilbertFullFiberPrincipal

/-!
# Restricting invariant regular norms to actual affine principal sources

A principal source contained in the full good open receives the regular norm
by restriction. The ORIGINAL restricted relation proves invariance there.
No extension of a function from the good open to the old affine source is used.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite Module
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve Approximation SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R)))
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} (k : A ⟶ variableHilbertTest f d V)

/-- Pulling back a compatible function preserves the original complete restricted relation. -/
theorem nestedInvariant_pullback {B : Over (Spec (.of R))} (v : B ⟶ A)
    (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left) :
    v.left.appTop s.val ∈
      compatibleFunctions (fst f hL d V c (v ≫ k)).left (snd f hL d V c (v ≫ k)).left := by
  have h := congrArg (nestedToFullRelation f hL d V c k v).left.appTop s.property
  change ((nestedToFullRelation f hL d V c k v ≫ fst f hL d V c k).left).appTop s.val =
    ((nestedToFullRelation f hL d V c k v ≫ snd f hL d V c k).left).appTop s.val at h
  rw [nestedToFullRelation_fst, nestedToFullRelation_snd] at h
  exact h

variable [IsOpenImmersion k.left] (r : Γ(A.left, ⊤))
  (hr : A.left.basicOpen r ≤ fullEnvelopeInterior f hL d V c k)

/-- The actual principal source maps into the nonaffine full good open. -/
def orbitPrincipalToInterior : orbitPrincipalSource r ⟶ fullInteriorSource f hL d V c k :=
  Over.homMk (A.left.homOfLE hr) (by
    change A.left.homOfLE hr ≫ _ ≫ A.hom = _ ≫ A.hom
    rw [Scheme.homOfLE_ι_assoc])

/-- This map retains the principal chart's original parameter. -/
theorem orbitPrincipalToInterior_chart :
    orbitPrincipalToInterior f hL d V c k r hr ≫ fullInteriorChart f hL d V c k =
      orbitPrincipalChart f d V k r := by
  unfold fullInteriorChart orbitPrincipalChart
  rw [← Category.assoc]
  congr 1
  apply Over.OverMorphism.ext
  exact Scheme.homOfLE_ι A.left hr

variable [IsAffine V.left] [Etale V.hom]
/-- The finite basis is for the original translation algebra. -/
local instance principalNormTranslationAlgebra : Algebra R Γ(V.left, ⊤) :=
  affineBaseSectionAlgebra V.hom
variable {ι : Type} [Finite ι] (b : Basis ι R Γ(V.left, ⊤))
  (s : Γ((fullInteriorSource f hL d V c k).left, ⊤))

/-- Restrict the constructed regular norm from the good open to the actual principal source. -/
def orbitPrincipalRegularNorm : Γ((orbitPrincipalSource r).left, ⊤) :=
  (orbitPrincipalToInterior f hL d V c k r hr).left.appTop
    (fullInteriorInvariantNorm f hL d V c k b s).val

/-- The restricted norm is invariant for the principal chart's ORIGINAL full relation. -/
theorem orbitPrincipalRegularNorm_invariant :
    orbitPrincipalRegularNorm f hL d V c k r hr b s ∈
      compatibleFunctions (fst f hL d V c (orbitPrincipalChart f d V k r)).left
        (snd f hL d V c (orbitPrincipalChart f d V k r)).left := by
  rw [← orbitPrincipalToInterior_chart f hL d V c k r hr]
  exact nestedInvariant_pullback f hL d V c (fullInteriorChart f hL d V c k)
    (orbitPrincipalToInterior f hL d V c k r hr) (fullInteriorInvariantNorm f hL d V c k b s)

/-- A coefficient in the actual invariant ring of the affine principal source. -/
def orbitPrincipalInvariantNorm :
    compatibleFunctions (fst f hL d V c (orbitPrincipalChart f d V k r)).left
      (snd f hL d V c (orbitPrincipalChart f d V k r)).left :=
  ⟨orbitPrincipalRegularNorm f hL d V c k r hr b s,
    orbitPrincipalRegularNorm_invariant f hL d V c k r hr b s⟩

end FLT.Mazur.HilbertChart.AffineRestriction
