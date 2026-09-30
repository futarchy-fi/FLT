/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ModuleCohomologyVanishing
public import FLT.Mazur.ProjectiveTwistQuotient
public import FLT.Mazur.ProjectiveTwistVanishing

/-! # Exact twisting and vanishing for twisted finite presentations -/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open FLT.Mazur.FCurve

universe u

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] (ι : Type u)

/-- Twisting preserves short exact sequences because it is an equivalence. -/
theorem twistTensor_shortExact (S : ShortComplex (space R ι).Modules)
    (hS : S.ShortExact) (n : ℤ) : (S.map (twistTensorFunctor R ι n)).ShortExact := by
  exact hS.map_of_exact (twistTensorEquivalence R ι n).functor

/-- Twisting a finite sum of twists adds the two degrees on each summand. -/
def twistTensorTwistSumIso (κ : Type u) (a n : ℤ) :
    twistTensor R ι (∐ fun _ : κ ↦ twistingSheaf R ι a) n ≅
      ∐ fun _ : κ ↦ twistingSheaf R ι (a + n) := by
  let G := (twistTensorEquivalence R ι n).functor
  exact PreservesCoproduct.iso G (fun _ : κ ↦ twistingSheaf R ι a) ≪≫
    Sigma.mapIso (fun _ : κ ↦ twistingSheafTensorIso R ι a n)

/-- A nonnegative total twist makes every positive cohomology group of the sum zero. -/
theorem twistTensor_twistSum_moduleH_subsingleton [Finite ι] {κ : Type u} [Finite κ]
    (a n : ℤ) (h : 0 ≤ a + n) (q : ℕ) :
    Subsingleton (ModuleH (twistTensor R ι
      (∐ fun _ : κ ↦ twistingSheaf R ι a) n) (q + 1)) := by
  let _summandZero : Subsingleton (ModuleH (twistingSheaf R ι (a + n)) (q + 1)) :=
    twist_moduleH_subsingleton_nonneg R ι (a + n) h q
  let _sumZero := moduleH_subsingleton_coproduct
    (fun _ : κ ↦ twistingSheaf R ι (a + n)) (q + 1)
  exact moduleH_subsingleton_of_iso (twistTensorTwistSumIso R ι κ a n) (q + 1)

end FLT.Mazur.ProjectiveSpace
