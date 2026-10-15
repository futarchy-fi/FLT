/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertPrincipalFiniteTests
public import FLT.Mazur.SchemeRelationPrincipalNumerator

/-!
# Original supports for invariants of recomputed principal Hilbert charts

The full relation isomorphism transports the local invariant equation, then
denominator clearing constructs an invariant in the ORIGINAL source ring.
Its principal open is exactly the image of the new coefficient's open.
The original principal denominator need not itself be admissible.
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
local notation "p" => Over.Hom.left (fst f hL d V c k)
local notation "q" => Over.Hom.left (snd f hL d V c k)
variable (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
local notation "B" => invariantPrincipalSource f hL d V c k s
local notation "u" => invariantPrincipalSourceMap f hL d V c k s
local notation "l" => invariantPrincipalChart f hL d V c k s
local instance principalSupport_open : IsOpenImmersion (u).left :=
  inferInstanceAs (IsOpenImmersion (A.left.basicOpen s.val).ι)

/-- Every recomputed invariant principal has its exact support in the OLD invariant ring. -/
theorem principalInvariant_exists_original_support
    (z : compatibleFunctions (fst f hL d V c l).left (snd f hL d V c l).left) :
    ∃ a : compatibleFunctions p q,
      A.left.basicOpen a.val = (u).left ''ᵁ (B).left.basicOpen z.val ∧
      A.left.basicOpen a.val ≤ A.left.basicOpen s.val := by
  unfold invariantPrincipalChart at z ⊢
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := relation_compactSpace f hL d V c k
  let _ := relation_quasiSeparatedSpace f hL d V c k
  let e := nestedSchemeDoubleIso f hL d V c k u
  have hz : z.val ∈ compatibleFunctions
      (SchemeRelationRestriction.fst p q (u).left)
      (SchemeRelationRestriction.snd p q (u).left) :=
    (relationIso_invariant_iff _ _ _ _ e
      (nestedSchemeDoubleIso_fst f hL d V c k u)
      (nestedSchemeDoubleIso_snd f hL d V c k u) z.val).mpr z.property
  exact SchemeRelationPrincipalLocalization.exists_full_invariant_support p q s ⟨z.val, hz⟩

end FLT.Mazur.HilbertChart.AffineRestriction
