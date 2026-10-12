/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartesianLineFieldCohomology
public import FLT.Mazur.ProperCohomologyFieldVanishing
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Geometric tests determine proper line cohomology on all field fibers

Extend the field to its algebraic closure and paste the actual family
squares. Proper field base change detects vanishing and preserves dimensions.
This argument works for varying families over an arbitrary base scheme.
-/

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules
namespace FLT.Mazur.FCurve
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

variable {X S : Scheme} (f : X ⟶ S) [IsProper f]
  (L : X.Modules) (hL : LocallyFreeRankOne L) (n : ℕ)

include hL in
/-- Actual geometric vanishing detects vanishing on every field-valued fiber. -/
theorem properLine_field_vanishing_of_geometric
    (hV : ∀ (K : Type) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S),
      Subsingleton (ModuleH ((Scheme.Modules.pullback (pullback.fst f b)).obj L) n))
    {k : Type} [Field k] (g : Spec (.of k) ⟶ S) :
    Subsingleton (ModuleH ((Scheme.Modules.pullback (pullback.fst f g)).obj L) n) := by
  let K := AlgebraicClosure k
  let a := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.fst f g
  let q := pullback.snd f g
  let H := IsPullback.of_hasPullback q a
  let H' := H.paste_horiz (IsPullback.of_hasPullback f g)
  let _ := hV K (a ≫ g)
  let _ := (cartesianLine_vanishing_iff H' L n).mp inferInstance
  let e := (pullbackComp (pullback.fst q a) p).app L
  have hv := proper_line_cohomology_field_vanishing_iff H (hL.pullback p) n
  change Subsingleton (ModuleH _ n) ↔ Subsingleton (ModuleH _ n) at hv
  exact hv.mp (moduleH_subsingleton_of_iso e n)

include hL in
/-- Exact geometric dimensions also determine all field-fiber dimensions. -/
theorem properLine_field_finrank_of_geometric (d : ℕ)
    (hD : ∀ (K : Type) [Field K] [IsAlgClosed K] (b : Spec (.of K) ⟶ S),
      Module.finrank K (ModuleScalarH (pullback.snd f b)
        ((Scheme.Modules.pullback (pullback.fst f b)).obj L) n) = d)
    {k : Type} [Field k] (g : Spec (.of k) ⟶ S) :
    Module.finrank k (ModuleScalarH (pullback.snd f g)
      ((Scheme.Modules.pullback (pullback.fst f g)).obj L) n) = d := by
  let K := AlgebraicClosure k
  let a := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let p := pullback.fst f g
  let q := pullback.snd f g
  let H := IsPullback.of_hasPullback q a
  let H' := H.paste_horiz (IsPullback.of_hasPullback f g)
  let M := (Scheme.Modules.pullback p).obj L
  let _ := (hL.pullback p).isFinitePresentation
  let e := (pullbackComp (pullback.fst q a) p).app L
  calc
    _ = Module.finrank K (ModuleScalarH (pullback.snd q a)
        ((Scheme.Modules.pullback (pullback.fst q a)).obj M) n) :=
      (proper_field_cohomology_finrank H M n).symm
    _ = Module.finrank K (ModuleScalarH (pullback.snd q a)
        ((Scheme.Modules.pullback (pullback.fst q a ≫ p)).obj L) n) :=
      ((moduleScalarHFunctor (pullback.snd q a) n).mapIso e).toLinearEquiv.finrank_eq
    _ = d := (cartesianLine_finrank H' L n).trans (hD K (a ≫ g))

end FLT.Mazur.FCurve
