/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.AcyclicPushforwardCohomology
public import FLT.Mazur.CoherentIdealIntersection

/-!
# Exactness and acyclicity of closed direct images

The stalkwise exactness of closed module pushforward applies to every module,
without coherence or Noetherian hypotheses. Applying it to an injective
resolution gives vanishing of the actual positive module higher direct images.
The module-to-abelian comparison supplies the corresponding abelian vanishing.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open AlgebraicGeometry.Scheme.Modules

universe u

namespace FLT.Mazur.ClosedDirectImageAcyclic

open FCurve

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f]

/-- Closed module pushforward preserves every exact short complex. -/
theorem map_exact (S : ShortComplex X.Modules) (hS : S.Exact) :
    (S.map (pushforward f)).Exact :=
  hS.map (pushforward f)

/-- Closed module pushforward preserves every short exact sequence. -/
theorem map_shortExact (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    (S.map (pushforward f)).ShortExact := by
  have := hS.mono_f
  have := hS.epi_g
  exact hS.map (pushforward f)

/-- Pushing an injective resolution along a closed immersion is exact in positive degrees. -/
lemma image_exact_succ (M : X.Modules) (I : InjectiveResolution M) (n : ℕ) :
    (((pushforward f).mapHomologicalComplex _).obj I.cocomplex).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (by simp) (by simp)]
  exact (I.exact_succ n).map (pushforward f)

/-- Every module has zero positive higher direct images under a closed immersion. -/
theorem isZero_rightDerived_obj (M : X.Modules) (n : ℕ) :
    IsZero (((pushforward f).rightDerived (n + 1)).obj M) := by
  let I := injectiveResolution M
  have h := (HomologicalComplex.exactAt_iff_isZero_homology _ _).1
    (image_exact_succ f M I n)
  exact h.of_iso (I.isoRightDerivedObj (pushforward f) (n + 1))

/-- Closed immersions supply the acyclicity input for the direct-image comparison. -/
theorem modulePushforwardAcyclic (M : X.Modules) : ModulePushforwardAcyclic f M :=
  isZero_rightDerived_obj f M

/-- Forgetting scalars gives the abelian acyclicity used by the open comparison. -/
theorem abelianPushforwardAcyclic (M : X.Modules) :
    AbsoluteDirectImageCohomology.Acyclic f.base (moduleAbelianSheaf M) :=
  modulePushforwardAcyclic_abelian f M (modulePushforwardAcyclic f M)

end FLT.Mazur.ClosedDirectImageAcyclic
