/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteEnvelopeKernel
public import FLT.Mazur.AffineHilbertSelectorQuotient

/-!+# Finite original kernels from invariant representatives

An invariant family of actual original arrows suffices to recover the entire
finite coefficient kernel. Equality of finite coefficients identifies their
affine representative endpoints; division then reconstructs the original
arrow. The independent translation envelope need not be full or affine.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
namespace FLT.Mazur.HilbertChart.AffineRestriction
open CartierAbel SchemePicard FCurve
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
attribute [local irreducible] relation fst snd
variable {R : Type} [CommRing R] [Algebra.FiniteType ℤ R] {X : Scheme}
  (f : X ⟶ Spec (.of R)) [IsProper f] [Flat f] [GeometricallyIntegral f]
  [SmoothOfRelativeDimension 1 f] {L : X.Modules} (hL : AmpleLineBundle L)
  (d : ℕ) (V : Over (Spec (.of R))) [Etale V.hom]
  (c : (relativeFppfSheaf f).obj.obj (op V))
  {A : Over (Spec (.of R))} [IsAffine A.left]
  (k : A ⟶ variableHilbertTest f d V) [IsOpenImmersion k.left]
local notation "p" => fst f hL d V c k
local notation "q" => snd f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c k
local notation "g" => selectorProjection f hL d V c k

/-- Finite original equations identify the constructed representative quotient. -/
theorem finiteKernel_eq_selector
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left)
    {T : Over (Spec (.of R))} (a b : T ⟶ A)
    (hab : a ≫ v = b ≫ v) : a ≫ g r hr hi = b ≫ g r hr hi := by
  have hh := finiteKernel_eq_affine_invariant f hL d V c k
    (r ≫ (q).left) hi a b hab
  apply Over.OverMorphism.ext
  apply (cancel_mono (SchemeRelationSelectorQuotient.inclusion («q» := q) r)).mp
  simpa only [Over.comp_left, selectorProjection, Over.homMk_left, Category.assoc,
    SchemeRelationSelectorQuotient.projection_inclusion] using hh

attribute [local irreducible] selectorProjection selectorTarget
  SchemeRelationSelectorQuotient.target SchemeRelationSelectorQuotient.projection

/-- The full relative Picard kernel follows from original arrows, without full envelopes. -/
theorem finiteSelector_relative_isPullback
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) : IsPullback p q v v := by
  have H : IsPullback p q (g r hr hi) (g r hr hi) := by
    apply IsPullback.of_map_of_faithful (Over.forget _)
    exact selectorProjection_isPullback f hL d V c k r hr hi
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (finiteKernelProjection_condition f hL d V c k)
    (fun t ↦ H.lift t.fst t.snd
      (finiteKernel_eq_selector f hL d V c k r hr hi t.fst t.snd t.condition))
    (fun _ ↦ H.lift_fst _ _ _) (fun _ ↦ H.lift_snd _ _ _) ?_)
  intro t b hb₁ hb₂
  apply hom_ext f hL d V c k
  · exact hb₁.trans (H.lift_fst _ _ _).symm
  · exact hb₂.trans (H.lift_snd _ _ _).symm

/-- The underlying scheme kernel retains every residue-field branch and nilpotent direction. -/
theorem finiteSelector_isPullback
    (r : A.left ⟶ (relation f hL d V c k).left)
    (hr : r ≫ (p).left = 𝟙 A.left)
    (hi : (p).left ≫ r ≫ (q).left = (q).left ≫ r ≫ (q).left) :
    IsPullback (p).left (q).left (v).left (v).left :=
  (finiteSelector_relative_isPullback f hL d V c k r hr hi).map (Over.forget _)

end FLT.Mazur.HilbertChart.AffineRestriction
