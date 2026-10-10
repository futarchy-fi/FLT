/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.TwistedSectionBaseChangeRegularity
public import FLT.Mazur.ProperLinePushforwardMate
public import Mathlib.AlgebraicGeometry.Geometrically.Integral

/-!
# Proper locally split sections are regular on geometric fibers

Residue cohomology vanishing supplies the actual base-change isomorphism.
A locally split original direct-image line then has a regular independently
pulled section on every field-valued fiber of a geometrically integral family.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.ProperSplitSectionFiberRegularity
open FCurve ModuleSheafTensor SplitLineAffineNeighborhood LineSectionBaseChange
open TwistedSectionBaseChangeRegularity
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
attribute [local irreducible] tensor twistedSectionPushforwardEquiv
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))
  {B : S.Modules} (hB : LocallyFreeRankOne B)
  (s : Γ(tensor L ((pullback f).obj B), ⊤))
  (hs : LocallySplit (twistedSectionPushforwardEquiv f L hB s))

include hL hV hs

/-- Proper cohomological base change gives regularity on an integral affine-base pullback. -/
theorem regular_on_integral_baseChange {P T : Scheme.{0}} [IsAffine T]
    [IsIntegral P] [Nonempty T] {p : P ⟶ X} {q : P ⟶ T} {g : T ⟶ S}
    (h : IsPullback p q f g) :
    Mono (globalSectionHom _ (section_ p q f g h.w.symm L s)) := by
  let _ := properLineBaseChangeMate_isIso h L hL hV
  exact regular_of_locallySplit p q f g h.w.symm L hB hL s hs

/-- Every field-valued fiber has a regular section in a geometrically integral family. -/
theorem regular_on_field_fiber [GeometricallyIntegral f]
    (K : Type) [Field K] (g : Spec (CommRingCat.of K) ⟶ S) :
    Mono (globalSectionHom _ (section_ (Limits.pullback.fst f g)
      (Limits.pullback.snd f g) f g Limits.pullback.condition.symm L s)) := by
  let _ : IsIntegral (Limits.pullback f g) :=
    pullback_of_geometrically
      (GeometricallyIntegral.geometrically_isIntegral (f := f)) K g
  exact regular_on_integral_baseChange f L hL hV hB s hs (IsPullback.of_hasPullback f g)

/-- In particular, the section on each actual scheme residue fiber is regular. -/
theorem regular_on_residue_fiber [GeometricallyIntegral f] (x : S) :
    Mono (globalSectionHom _ (section_ (Limits.pullback.fst f (S.fromSpecResidueField x))
      (Limits.pullback.snd f (S.fromSpecResidueField x)) f (S.fromSpecResidueField x)
        Limits.pullback.condition.symm L s)) :=
  regular_on_field_fiber f L hL hV hB s hs (S.residueField x) (S.fromSpecResidueField x)

end FLT.Mazur.ProperSplitSectionFiberRegularity
