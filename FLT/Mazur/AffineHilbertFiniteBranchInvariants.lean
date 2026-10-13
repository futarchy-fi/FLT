/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteBranchAtlas
public import FLT.Mazur.SchemeFppfCoverInvariantFunctions
public import FLT.Mazur.SchemeRelationIsoInvariants

/-!
# Full Hilbert invariants computed on the constructed finite branches

The simultaneous coefficient equations on the actual branch atlas detect
exactly the full original relation. Their solutions give invariant affine
principal opens. No single branch is assumed closed under composition.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve SchemeEffectiveEpiSections
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "D" => relation f hL d V c k
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "Z" => EtaleFiniteBranchAtlas.source p
local notation "a" => EtaleFiniteBranchAtlas.original p

/-- Pull regular functions to all first endpoints, in the original branch coefficient rings. -/
def finiteBranchFirst : Γ(A.left, ⊤) →+* (∀ r : (D).left, Γ((Z r).left, ⊤)) :=
  RingHom.pi fun r ↦ (a r ≫ p).left.appTop.hom

/-- Pull regular functions to all independent second endpoints of the same branches. -/
def finiteBranchSecond : Γ(A.left, ⊤) →+* (∀ r : (D).left, Γ((Z r).left, ⊤)) :=
  RingHom.pi fun r ↦ (a r ≫ q).left.appTop.hom

/-- The constructed simultaneous branch equations recover the full original invariant ring. -/
theorem finiteBranch_eqLocus :
    RingHom.eqLocus (finiteBranchFirst f hL d V c k) (finiteBranchSecond f hL d V c k) =
      compatibleFunctions (p).left (q).left := by
  ext s
  change (fun r ↦ (a r ≫ p).left.appTop s) =
    (fun r ↦ (a r ≫ q).left.appTop s) ↔ _
  rw [funext_iff]
  exact (SchemeFppfFamily.mem_compatibleFunctions_iff
    (finiteBranchFppfCover f hL d V c k) (p).left (q).left s).symm

/-- Scheme-valued maps satisfy the full relation if and only if all branch equations hold. -/
theorem finiteBranch_coequalizes_iff {Y : Scheme} (g : A.left ⟶ Y) :
    (p).left ≫ g = (q).left ≫ g ↔
      ∀ r : (D).left, (a r ≫ p).left ≫ g = (a r ≫ q).left ≫ g := by
  change _ ↔ ∀ r, (a r).left ≫ (p).left ≫ g = (a r).left ≫ (q).left ≫ g
  exact SchemeFppfFamily.coequalizes_iff (finiteBranchFppfCover f hL d V c k)
      (p).left (q).left g

/-- A solution of the constructed branch equations defines an actual full-invariant affine open. -/
theorem finiteBranch_solution_affine (s : Γ(A.left, ⊤))
    (hs : finiteBranchFirst f hL d V c k s = finiteBranchSecond f hL d V c k s) :
    IsAffineOpen (A.left.basicOpen s) ∧
      (p).left ⁻¹ᵁ A.left.basicOpen s = (q).left ⁻¹ᵁ A.left.basicOpen s := by
  have hm : s ∈ compatibleFunctions (p).left (q).left := by
    rw [← finiteBranch_eqLocus f hL d V c k]
    exact hs
  exact ⟨(isAffineOpen_top A.left).basicOpen s,
    compatibleFunctions_basicOpen (p).left (q).left ⟨s, hm⟩⟩

end FLT.Mazur.HilbertChart.AffineRestriction
