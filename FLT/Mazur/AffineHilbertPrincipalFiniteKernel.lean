/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertPrincipalFiniteTests

/-!
# Transporting principal Picard kernels to the original finite model

The old finite model restricted to an invariant principal source has exactly
the kernel of the freshly recomputed finite model. Construct the actual kernel
isomorphism with both endpoints fixed, and transfer effectivity back to the
old coefficients. This identifies kernels, not coefficient target schemes.
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
  (s : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
local notation "u" => invariantPrincipalSourceMap f hL d V c k s
local notation "l" => invariantPrincipalChart f hL d V c k s
local notation "w" => u ≫ finiteKernelProjection f hL d V c k
local notation "v" => finiteKernelProjection f hL d V c l
local notation "p" => fst f hL d V c l
local notation "q" => snd f hL d V c l

/-- Both original endpoints have the same OLD finite coefficients on the principal source. -/
@[reassoc]
theorem principalOldFinite_condition : p ≫ w = q ≫ w := by
  simpa only [Category.assoc] using
    (principalFinite_test_iff f hL d V c k s p q).mp
      (finiteKernelProjection_condition f hL d V c l)

/-- The full recomputed and old restricted finite kernels are isomorphic over both endpoints. -/
def principalFiniteKernelIso : pullback v v ≅ pullback w w where
  hom := pullback.lift (pullback.fst v v) (pullback.snd v v) (by
    simpa only [Category.assoc] using
      (principalFinite_test_iff f hL d V c k s _ _).mp pullback.condition)
  inv := pullback.lift (pullback.fst w w) (pullback.snd w w)
    ((principalFinite_test_iff f hL d V c k s _ _).mpr (by
      simpa only [Category.assoc] using pullback.condition (f := w) (g := w)))
  hom_inv_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]
  inv_hom_id := by
    apply pullback.hom_ext <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.id_comp]

/-- The kernel comparison retains the entire first original source morphism. -/
@[reassoc]
theorem principalFiniteKernelIso_fst :
    (principalFiniteKernelIso f hL d V c k s).hom ≫ pullback.fst w w = pullback.fst v v :=
  pullback.lift_fst _ _ _

/-- The second coordinate is retained independently, including residue fields and nilpotents. -/
@[reassoc]
theorem principalFiniteKernelIso_snd :
    (principalFiniteKernelIso f hL d V c k s).hom ≫ pullback.snd w w = pullback.snd v v :=
  pullback.lift_snd _ _ _

/-- A proved fresh principal kernel reconstructs the full kernel of the OLD finite coefficients. -/
theorem principalOldFinite_relative_isPullback (H : IsPullback p q v v) :
    IsPullback p q w w := by
  refine IsPullback.of_isLimit (PullbackCone.IsLimit.mk
    (principalOldFinite_condition f hL d V c k s)
    (fun t ↦ H.lift t.fst t.snd
      ((principalFinite_test_iff f hL d V c k s t.fst t.snd).mpr (by
        simpa only [Category.assoc] using t.condition)))
    (fun _ ↦ H.lift_fst _ _ _) (fun _ ↦ H.lift_snd _ _ _) ?_)
  intro t b hb₁ hb₂
  apply hom_ext f hL d V c l
  · exact hb₁.trans (H.lift_fst _ _ _).symm
  · exact hb₂.trans (H.lift_snd _ _ _).symm

/-- Forgetting the base preserves the entire old coefficient-kernel reconstruction. -/
theorem principalOldFinite_isPullback
    (H : IsPullback (p).left (q).left (v).left (v).left) :
    IsPullback (p).left (q).left (w).left (w).left :=
  (principalOldFinite_relative_isPullback f hL d V c k s
    (IsPullback.of_map_of_faithful (Over.forget _) H)).map (Over.forget _)

end FLT.Mazur.HilbertChart.AffineRestriction
