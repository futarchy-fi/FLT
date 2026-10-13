/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertInvariantFiniteType
public import FLT.Mazur.FiniteCoefficientDifferenceIdeal
public import FLT.Mazur.SchemeRelationInvariantTestEquality

/-!
# Finite original invariant equations for the actual candidate kernel

The original coefficient-base product is affine and Noetherian. Finitely many
actual invariant coefficient differences therefore detect its full candidate
kernel on every scheme test. No finite generation of the invariant ring, and
no equality with the original Picard relation, is inferred.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
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
local notation "B" => compatibleFunctions
  (Over.Hom.left (FLT.Mazur.HilbertChart.AffineRestriction.fst f hL d V c k))
  (Over.Hom.left (FLT.Mazur.HilbertChart.AffineRestriction.snd f hL d V c k))
local notation "P" => prod A A

include k in
/-- The original coefficient-base product has a Noetherian global section ring. -/
theorem coefficientPairRing_isNoetherian : IsNoetherianRing Γ((P).left, ⊤) := by
  let _ := selectedHilbertSource_isLocallyNoetherian f d V k
  let _ := selectedSource_locallyOfFiniteType f d V k
  let _ : LocallyOfFiniteType (prod.fst : P ⟶ A).left := by
    rw [← Over.prodLeftIsoPullback_hom_fst]
    infer_instance
  let _ := LocallyOfFiniteType.isLocallyNoetherian (prod.fst : P ⟶ A).left
  let _ : IsAffine (P).left := IsAffine.of_isIso (Over.prodLeftIsoPullback A A).hom
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

/-- The first actual invariant coefficient map on the original base product. -/
def invariantKernelLeftCoefficients : B →+* Γ((P).left, ⊤) :=
  (prod.fst : P ⟶ A).left.appTop.hom.comp (B).subtype

/-- The independent second actual invariant coefficient map. -/
def invariantKernelRightCoefficients : B →+* Γ((P).left, ⊤) :=
  (prod.snd : P ⟶ A).left.appTop.hom.comp (B).subtype

local notation "l" => invariantKernelLeftCoefficients f hL d V c k
local notation "r" => invariantKernelRightCoefficients f hL d V c k

/-- Finitely many ORIGINAL invariant coefficients cut out the entire candidate kernel. -/
def finiteKernelCoefficients : Finset B := by
  let _ := coefficientPairRing_isNoetherian f d V k
  exact FiniteCoefficientDifference.coefficients l r

/-- The finite equations generate the full scheme-theoretic coefficient equality ideal. -/
theorem finiteKernelCoefficients_ideal :
    FiniteCoefficientDifference.differenceIdeal l r =
      Ideal.span ((fun s ↦ l s - r s) '' (finiteKernelCoefficients f hL d V c k : Set B)) := by
  let _ := coefficientPairRing_isNoetherian f d V k
  exact FiniteCoefficientDifference.differenceIdeal_eq l r

/-- Every scheme test sees exactly the full candidate kernel through these finite equations. -/
theorem finiteKernelCoefficients_test {T : Over (Spec (.of R))} (a b : T ⟶ A) :
    a ≫ invariantAffineProjection f hL d V c k =
        b ≫ invariantAffineProjection f hL d V c k ↔
      ∀ s ∈ finiteKernelCoefficients f hL d V c k,
        a.left.appTop s.val = b.left.appTop s.val := by
  let _ := coefficientPairRing_isNoetherian f d V k
  have hp : a ≫ invariantAffineProjection f hL d V c k =
      b ≫ invariantAffineProjection f hL d V c k ↔
        ∀ s : B, a.left.appTop s.val = b.left.appTop s.val := by
    constructor
    · intro h
      exact (SchemeRelationInvariantSpectrum.projection_test_eq_iff _ _ a.left b.left).mp
        (congrArg Over.Hom.left h)
    · intro h
      apply Over.OverMorphism.ext
      exact (SchemeRelationInvariantSpectrum.projection_test_eq_iff _ _ a.left b.left).mpr h
  rw [hp]
  let g := (prod.lift a b).left.appTop.hom
  have hl (s : B) : g (l s) = a.left.appTop s.val := by
    change ((prod.fst : P ⟶ A).left.appTop ≫ (prod.lift a b).left.appTop) s.val = _
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, prod.lift_fst]
  have hr (s : B) : g (r s) = b.left.appTop s.val := by
    change ((prod.snd : P ⟶ A).left.appTop ≫ (prod.lift a b).left.appTop) s.val = _
    rw [← Scheme.Hom.comp_appTop, ← Over.comp_left, prod.lift_snd]
  have ht := FiniteCoefficientDifference.equalizes_iff_coefficients l r g
  rw [RingHom.ext_iff] at ht
  simpa only [RingHom.comp_apply, hl, hr, finiteKernelCoefficients] using ht

/-- Solutions of the finite equations lift uniquely to the actual full scheme kernel. -/
theorem finiteKernelCoefficients_lift {T : Over (Spec (.of R))} (a b : T ⟶ A)
    (h : ∀ s ∈ finiteKernelCoefficients f hL d V c k,
      a.left.appTop s.val = b.left.appTop s.val) :
    ∃! t : T ⟶ pullback (invariantAffineProjection f hL d V c k)
        (invariantAffineProjection f hL d V c k),
      t ≫ pullback.fst _ _ = a ∧ t ≫ pullback.snd _ _ = b := by
  let e := (finiteKernelCoefficients_test f hL d V c k a b).mpr h
  refine ⟨pullback.lift a b e, ⟨pullback.lift_fst _ _ _, pullback.lift_snd _ _ _⟩, ?_⟩
  intro t ht
  apply pullback.hom_ext
  · exact ht.1.trans (pullback.lift_fst _ _ _).symm
  · exact ht.2.trans (pullback.lift_snd _ _ _).symm

end FLT.Mazur.HilbertChart.AffineRestriction
