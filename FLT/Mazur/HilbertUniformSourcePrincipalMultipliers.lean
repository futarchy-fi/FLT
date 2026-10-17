/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.HilbertUniformSourceBoundaryDescent
public import FLT.Mazur.HilbertBoundaryLiftLocus

/-!
# Fixed-domain original multipliers from uniform source neighborhoods

An original invariant principal open contained in a constructed uniform orbit
neighborhood admits exact boundary lifts. Clearing this original denominator
produces a power multiplier and a lift on the fixed original domain. Existence
of such denominators at every required point is not assumed or asserted.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve EquivalenceRelationNormalizedFrames
open RelativeRelationOrbit InvariantOpenRelationDiagram
open FiniteGroupRestriction SchemeFiniteGroupQuotient
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [IsAffine V.left] [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => Over.Hom.left (AffineRestriction.fst f hL d V c k)
local notation "q" => Over.Hom.left (AffineRestriction.snd f hL d V c k)
local notation "e" => fullRelationSchemeEquivalence f hL d V c k
local notation "eo" => equivalence f hL d V c k
local notation "ec" => originalClosedEquivalence f hL d V c k
local notation "m" => originalClosedInvariantMap f hL d V c k
variable (n : ℕ) (o : Fin n)
  (U : (normalizedFullRelationFrames f hL d V c k n o).Opens)
  (hU : ∀ σ : Equiv.Perm (Fin n),
    (normalizedFullRelationAction f hL d V c k n o σ).hom ⁻¹ᵁ U = U)
attribute [local irreducible] relation AffineRestriction.fst AffineRestriction.snd equivalence
  EquivalenceRelationNormalizedFrames.source relativeFppfSheaf AmpleLineBundle
attribute [local irreducible] RelativeRelationOrbit.orbitSetoid
  RelativeRelationOrbit.pullOpen
attribute [local irreducible] EquivalenceRelationNormalizedFrames.action
  uniformSourceOpen orbitImageOpen etaleSourceImage
set_option quotPrecheck false
local notation "B" => uniformSourceOpen e (Fin n) o U hU
local notation "j" => (B).ι ≫ U.ι ≫ normalizedFullRelationFirst f hL d V c k n o
local notation "r" => SchemeRelationRestriction.fst p q j
local notation "s" => SchemeRelationRestriction.snd p q j
local notation "O" => orbitImageOpen eo (q).isOpenMap (etaleSourceImage j)

attribute [local irreducible] originalBoundarySource originalBoundarySourceMap
  originalClosedRelation originalClosedFst originalClosedSnd originalClosedArrow
  originalClosedEquivalence
local notation "Wc" w:max => (TopologicalSpace.Opens.map (m).base).obj w

/-- A principal subneighborhood of the uniform orbit image lifts the original section exactly. -/
theorem uniformSource_original_principal_lift
    (W : TopologicalSpace.Opens (Orbit eo))
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val)
    (ha : IsAffineOpen U) (v : (invariantSheaf eo).obj.obj (op W))
    (hv : invariantPrincipal eo W v ≤ O)
    (t : (invariantSheaf ec).obj.obj (op (Wc W))) :
    ∃ b : (invariantSheaf eo).obj.obj (op (invariantPrincipal eo W v)),
      (m).c.app (op (invariantPrincipal eo W v)) b =
        (invariantSheaf ec).obj.map ((TopologicalSpace.Opens.map (m).base).map
          (homOfLE (invariantPrincipal_le eo W v))).op t := by
  obtain ⟨b, hb⟩ := uniformSource_original_boundary_lift f hL d V c k n o U hU W hUW ha t
  refine ⟨(invariantSheaf eo).obj.map (homOfLE hv).op b, ?_⟩
  have hn := congrArg (fun F ↦ F b) ((m).c.naturality (homOfLE hv).op)
  change (m).c.app _ ((invariantSheaf eo).obj.map _ b) = _ at hn
  rw [hn, ConcreteCategory.comp_apply, hb]
  change ((invariantSheaf ec).obj.map _ ≫ (invariantSheaf ec).obj.map _) t = _
  rw [← Functor.map_comp]
  rfl

/-- Clearing an actual original denominator gives a power lift on the unchanged fixed domain. -/
theorem uniformSource_original_power_lift
    (W : TopologicalSpace.Opens (Orbit eo))
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val)
    (ha : IsAffineOpen U) (hW : IsAffineOpen (pullOpen eo W).val)
    (v : (invariantSheaf eo).obj.obj (op W)) (hv : invariantPrincipal eo W v ≤ O)
    (t : (invariantSheaf ec).obj.obj (op (Wc W))) :
    ∃ (N : ℕ) (b : (invariantSheaf eo).obj.obj (op W)),
      (m).c.app (op W) b = originalClosedSectionPullback f hL d V c k W v ^ N * t :=
  (originalClosed_principal_lift_iff f hL d V c k W hW v t).mp
    (uniformSource_original_principal_lift f hL d V c k n o U hU W hUW ha v hv t)

/-- Each original principal subneighborhood lies in the fixed-domain multiplier lifting locus. -/
theorem uniformSource_original_principal_le_liftOpen
    (W : TopologicalSpace.Opens (Orbit eo))
    (hUW : U ≤ normalizedFullRelationFirst f hL d V c k n o ⁻¹ᵁ (pullOpen eo W).val)
    (ha : IsAffineOpen U) (hW : IsAffineOpen (pullOpen eo W).val)
    (v : (invariantSheaf eo).obj.obj (op W)) (hv : invariantPrincipal eo W v ≤ O)
    (t : (invariantSheaf ec).obj.obj (op (Wc W))) :
    invariantPrincipal eo W v ≤ originalBoundaryLiftOpen f hL d V c k W t := by
  intro x hx
  apply (mem_originalBoundaryLiftOpen_iff f hL d V c k W t hW x).mpr
  obtain ⟨N, b, hb⟩ :=
    uniformSource_original_power_lift f hL d V c k n o U hU W hUW ha hW v hv t
  exact ⟨v, hx, N, (originalClosedSectionObstruction_eq_zero_iff
    f hL d V c k W hW _).mpr ⟨b, hb⟩⟩

end FLT.Mazur.HilbertChart.AffineRestriction
