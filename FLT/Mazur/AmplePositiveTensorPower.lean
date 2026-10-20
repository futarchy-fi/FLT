/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperAmpleConverse
public import FLT.Mazur.TensorPowerGeneratorOpen
public import FLT.Mazur.DivisorLineBundlePower
public import FLT.Mazur.RelativeAmplePresentationTransport

/-!
# Ampleness of positive powers of actual divisor lines

Taking a positive power of each covering section retains its affine generator
open. This proves section ampleness of positive tensor powers, and properness
then supplies the required closed projective presentations.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Scheme.Modules

namespace FLT.Mazur.FCurve

open ModuleLineBundleTensorPullback

variable {X S : Scheme} {L : X.Modules}

/-- Every positive tensor power of an ample invertible sheaf is ample. -/
theorem AmpleLineBundle.positiveTensorPower (hL : AmpleLineBundle L) {n : ℕ} (hn : 0 < n) :
    AmpleLineBundle (tensorPower L n) := by
  refine ⟨hL.1, hL.2.1.tensorPower n, fun x ↦ ?_⟩
  obtain ⟨d, hd, s, hx, hs⟩ := hL.2.2 x
  let e : tensorPower (tensorPower L d) n ≅ tensorPower (tensorPower L n) d :=
    tensorPowerMulIso L d n ≪≫ eqToIso (congrArg (tensorPower L) (Nat.mul_comm d n)) ≪≫
      (tensorPowerMulIso L n d).symm
  let t := tensorPowerSection (tensorPower L d) ⊤ s n
  have he : sectionGeneratorOpen (tensorPower (tensorPower L n) d) (e.hom.app ⊤ t) =
      sectionGeneratorOpen (tensorPower L d) s := by
    rw [sectionGeneratorOpen_iso]
    exact tensorPowerSection_generatorOpen (hL.2.1.tensorPower d) s hn
  refine ⟨d, hd, e.hom.app ⊤ t, ?_, ?_⟩
  · rwa [he]
  · rwa [he]

/-- Positive tensor powers preserve ampleness on every affine base restriction. -/
theorem RelativelyAmpleLineBundle.positiveTensorPower {f : X ⟶ S}
    (hL : RelativelyAmpleLineBundle f L) {n : ℕ} (hn : 0 < n) :
    RelativelyAmpleLineBundle f (tensorPower L n) := by
  refine ⟨hL.1, hL.2.1.tensorPower n, fun U hU ↦ ?_⟩
  exact ((hL.2.2 U hU).positiveTensorPower hn).of_iso
    (tensorPowerRestrictIso L (f ⁻¹ᵁ U).ι n)

/-- Closed projective power presentations persist after any positive tensor power. -/
theorem RelativeAmple.positiveTensorPower {f : X ⟶ S}
    (hL : RelativeAmple f L) (hline : LocallyFreeRankOne L) {n : ℕ} (hn : 0 < n) :
    RelativeAmple f (tensorPower L n) := by
  let _ : IsProper f := hL.isProper
  exact ((hL.relativelyAmpleLineBundle hline).positiveTensorPower hn).relativeAmple

/-- The actual line of a positive power of an ample Cartier ideal is relatively ample. -/
theorem RelativeAmple.divisorPower {f : X ⟶ S} {I : X.IdealSheafData}
    (hI : EffectiveCartier I) (hL : RelativeAmple f (divisorLineBundle I hI))
    {n : ℕ} (hn : 0 < n) :
    RelativeAmple f (divisorLineBundle (I ^ n) (hI.pow n)) := by
  exact (hL.positiveTensorPower hI.divisorLineBundle_locallyFreeRankOne hn).of_iso
    (divisorLineBundlePowerIso hI n).symm

end FLT.Mazur.FCurve
