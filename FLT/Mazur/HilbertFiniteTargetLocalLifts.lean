/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertFiniteDomainErrorVanishing
public import FLT.Mazur.HilbertFiniteInvariantAffineBasis

/-!
# Actual original boundary section lifts near finite-locus points

Constructed affine invariant refinements give genuine local lifts of sections
on any original orbit domain. The section is restricted from that unchanged
domain; neither global affineness nor independent lift gluing is asserted.
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

variable [IsAffine V.left]
attribute [local irreducible] relativeFppfSheaf AmpleLineBundle
  EquivalenceRelationNormalizedFrames.source invariantSheaf sourceSheaf

variable (W : TopologicalSpace.Opens (Orbit (equivalence f hL d V c k)))
  (t : (invariantSheaf (originalClosedEquivalence f hL d V c k)).obj.obj
    (op ((TopologicalSpace.Opens.map
      (originalClosedInvariantMap f hL d V c k).base).obj W)))

/-- Finite affine domains give actual original lifts on smaller original orbit neighborhoods. -/
theorem exists_originalBoundary_lift_on_finiteDomain
    (hW : IsAffineOpen (pullOpen e W).val)
    (hf : (pullOpen e W).val ≤ finiteTargetOpen (p).left)
    (x : Orbit e) (hx : x ∈ W) :
    ∃ (Z : TopologicalSpace.Opens (Orbit e)) (hZW : Z ≤ W), x ∈ Z ∧
      ∃ a : (invariantSheaf e).obj.obj (op Z), (m).c.app (op Z) a =
        (invariantSheaf ec).obj.map
          ((TopologicalSpace.Opens.map (m).base).map (homOfLE hZW)).op t := by
  have hx' : x ∈ originalBoundaryLiftOpen f hL d V c k W t := by
    rw [originalBoundaryLiftOpen_eq_of_finiteDomain f hL d V c k W hW hf]
    exact hx
  obtain ⟨v, hxs, a, ha⟩ := (mem_principalLiftOpen_iff e ec (i).left (z).left
    (originalClosedArrow_left_fst f hL d V c k)
    (originalClosedArrow_left_snd f hL d V c k) W t hW
    ((p).left.isCompact_preimage hW.isCompact) x).mp hx'
  exact ⟨invariantPrincipal e W v, invariantPrincipal_le e W v, hxs, a, ha⟩

/-- Every original section has an actual local lift at every original finite-locus point. -/
theorem exists_originalBoundary_local_lift_of_finiteTarget
    (x : A.left) (hx : projection e x ∈ W) (hf : x ∈ finiteTargetOpen (p).left) :
    ∃ (Z : TopologicalSpace.Opens (Orbit e)) (hZW : Z ≤ W), projection e x ∈ Z ∧
      ∃ a : (invariantSheaf e).obj.obj (op Z), (m).c.app (op Z) a =
        (invariantSheaf ec).obj.map
          ((TopologicalSpace.Opens.map (m).base).map (homOfLE hZW)).op t := by
  obtain ⟨U, hxU, hUW, haU, hfU⟩ :=
    exists_originalFiniteAffine_neighborhood f hL d V c k W x hx hf
  let tU := (invariantSheaf ec).obj.map
    ((TopologicalSpace.Opens.map (m).base).map (homOfLE hUW)).op t
  obtain ⟨Z, hZU, hxZ, a, ha⟩ := exists_originalBoundary_lift_on_finiteDomain
    f hL d V c k U tU haU hfU (projection e x) hxU
  refine ⟨Z, hZU.trans hUW, hxZ, a, ?_⟩
  simpa only [tU, ← ConcreteCategory.comp_apply, ← Functor.map_comp,
    ← op_comp, homOfLE_comp] using ha

end FLT.Mazur.HilbertChart.AffineRestriction
