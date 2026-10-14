/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AffineHilbertFiniteEnvelopeEffective
public import FLT.Mazur.AffineHilbertInvariantPrincipalEffectiveness

/-!
# Finite-model kernel certificates from actual admissible coefficients

An original admissible invariant coefficient constructs a principal Hilbert
source whose full envelope is effective. Its freshly constructed finite model
therefore has the full original Picard kernel. The envelope isomorphism and
all seed certificates are derived, rather than new geometric premises.
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
  (r : compatibleFunctions (fst f hL d V c k).left (snd f hL d V c k).left)
  (hr : r ∈ invariantEnvelopeDenominators f hL d V c k)
local notation "k'" => invariantPrincipalChart f hL d V c k r
local notation "v" => finiteKernelProjection f hL d V c k'
local notation "h" => congrArg Over.Hom.left (finiteKernelProjection_condition f hL d V c k')
local notation "p" => Over.Hom.left (fst f hL d V c k')
local notation "q" => Over.Hom.left (snd f hL d V c k')

include hr in
/-- The new finite coefficient model has the complete original restricted Picard relation. -/
theorem admissibleFinite_isPullback : IsPullback p q (v).left (v).left := by
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  exact finiteEnvelope_isPullback f hL d V c k'

/-- Every arbitrary seed has a constructed original arrow on its entire finite-model kernel. -/
def admissibleFiniteSeedInverse {Z : Scheme}
    (a : Z ⟶ (invariantPrincipalSource f hL d V c k r).left) :
    pullback (a ≫ (v).left) (a ≫ (v).left) ⟶
      SchemeRelationRestriction.doubleDomain p q a :=
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  finiteEnvelopeSeedInverse f hL d V c k' a

/-- The nonsplit certificate retains both seed coordinates and the original coefficient map. -/
@[reassoc]
theorem admissibleFiniteSeedInverse_comp {Z : Scheme}
    (a : Z ⟶ (invariantPrincipalSource f hL d V c k r).left) :
    admissibleFiniteSeedInverse f hL d V c k r hr a ≫
      SchemeRelationSeedKernelTransport.seedComparison (v).left h a = 𝟙 _ := by
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  exact finiteEnvelopeSeedInverse_comp f hL d V c k' a

include hr in
/-- The complete original finite target is effective; no image or flatness assertion is added. -/
theorem admissibleFinite_effectiveTargetOpen_top :
    KernelPairEffectiveOpen.targetOpen p q (v).left h = ⊤ := by
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  exact finiteEnvelope_effectiveTargetOpen_top f hL d V c k'

include hr in
/-- A nonvanishing original point yields a nonempty effective finite-model neighborhood. -/
theorem admissibleFinite_effectiveTarget_nonempty (x : A.left)
    (hx : x ∈ A.left.basicOpen r.val) :
    Nonempty (modelEffectiveTarget f hL d V c k' v h).left := by
  let _ := invariantPrincipal_toEnvelope_isIso f hL d V c k r hr
  let _ : Nonempty (invariantPrincipalSource f hL d V c k r).left := ⟨⟨x, hx⟩⟩
  exact finiteEnvelope_effectiveTarget_nonempty f hL d V c k'

end FLT.Mazur.HilbertChart.AffineRestriction
