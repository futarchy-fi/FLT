/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.FlatGlobalGenerationDescent
public import FLT.Mazur.GlobalGenerationTransport
public import FLT.Mazur.AffineFpqcRefinement

/-!
# Fpqc descent of global generation over an affine base

Refining the covering scheme to an affine faithfully flat cover allows the
finite expansion argument to apply even when the original cover is not affine.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry Opposite
open Scheme.Modules
namespace FLT.Mazur.FpqcGlobalGenerationDescent
open FCurve ProjectiveSpace GlobalGenerationTransport
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {P X T S : Scheme} [CompactSpace X] [X.IsSeparated] [IsAffine S]
  {p : P ⟶ X} {q : P ⟶ T} {f : X ⟶ S} {g : T ⟶ S}
  [Flat g] [Surjective g] [QuasiCompact g]
  (h : IsPullback p q f g) (M : X.Modules) [M.IsQuasicoherent]

include h in
/-- An arbitrary fpqc cover of an affine base detects global generation. -/
theorem globalEvaluation_epi
    [Epi (globalEvaluation ((pullback p).obj M) (fun s : Γ((pullback p).obj M, ⊤) ↦ s))] :
    Epi (globalEvaluation M (fun s : Γ(M, ⊤) ↦ s)) := by
  obtain ⟨Z, hZ, k, hkf, hks⟩ := exists_affine_fpqc_refinement g
  let := hZ
  let := hkf
  let := hks
  let a := Limits.pullback.fst q k
  let b := Limits.pullback.snd q k
  have hs : IsPullback a b q k := IsPullback.of_hasPullback q k
  have := all_epi_pullback a ((pullback p).obj M)
  let e : (pullback a).obj ((pullback p).obj M) ≅ (pullback (a ≫ p)).obj M :=
    (pullbackComp a p).app M
  have := all_epi_of_iso e
  exact FlatGlobalGenerationDescent.globalEvaluation_epi (hs.paste_horiz h) M

include h in
/-- Generation by global sections is invariant under fpqc base change over an affine base. -/
theorem globalEvaluation_epi_iff :
    Epi (globalEvaluation ((pullback p).obj M) (fun s : Γ((pullback p).obj M, ⊤) ↦ s)) ↔
      Epi (globalEvaluation M (fun s : Γ(M, ⊤) ↦ s)) :=
  ⟨fun _ ↦ globalEvaluation_epi h M, fun _ ↦ all_epi_pullback p M⟩

end FLT.Mazur.FpqcGlobalGenerationDescent
