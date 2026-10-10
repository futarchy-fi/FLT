/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ProperLineAcyclicNeighborhood
public import FLT.Mazur.ProperLineRankOneOpenFactorization

/-!
# Rank-one representing opens near an acyclic fiber

Starting only with vanishing at one residue fiber, construct a principal
neighborhood and its actual rank-one direct-image open. On every test scheme,
the direct image is a line precisely when the test factors uniquely through
that open. The required neighborhood vanishing is derived, not assumed.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.LineSectionBaseChange
open FCurve Chow

variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] (L : X.Modules) (hL : LocallyFreeRankOne L)

include hL in
/-- Acyclicity at one fiber constructs a principal neighborhood's actual representing open. -/
theorem exists_principal_rankOne_representing_open (z : PrimeSpectrum Γ(S, ⊤))
    (hz : ∀ n, Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1))) :
    ∃ r ∉ z.asIdeal,
      let g := AffineBaseChangeCoefficients.baseMap S (Localization.Away r)
      let p := Limits.pullback.fst f g
      let q := Limits.pullback.snd f g
      let N := (pullback p).obj L
      ∃ V : (Spec (.of (Localization.Away r))).Opens,
        (∀ n, Subsingleton (ModuleH N (n + 1))) ∧
        ∀ (P T : Scheme.{0}) (a : P ⟶ Limits.pullback f g) (b : P ⟶ T)
          (c : T ⟶ Spec (.of (Localization.Away r))), IsPullback a b q c →
          (LocallyFreeRankOne ((pushforward b).obj ((pullback a).obj N)) ↔
            ∃! t : T ⟶ V.toScheme, t ≫ V.ι = c) := by
  obtain ⟨r, hr, hN⟩ := exists_principal_positive_vanishing f L hL z hz
  refine ⟨r, hr, ?_⟩
  let T := Spec (.of (Localization.Away r))
  let g := AffineBaseChangeCoefficients.baseMap S (Localization.Away r)
  let p := Limits.pullback.fst f g
  let q := Limits.pullback.snd f g
  let N := (pullback p).obj L
  have hn : LocallyFreeRankOne N := hL.pullback p
  let _ : IsNoetherianRing Γ(T, ⊤) :=
    isNoetherianRing_of_ringEquiv (Localization.Away r)
      (Scheme.ΓSpecIso (.of (Localization.Away r))).symm.commRingCatIsoToRingEquiv
  let _ := Chow.source_isNoetherian (q ≫ T.isoSpec.hom)
  let _ : (Limits.pullback f g).IsSeparated := ⟨by
    rw [← Limits.terminal.comp_from q]
    infer_instance⟩
  have hv (w : PrimeSpectrum Γ(T, ⊤)) (n : ℕ) :
      Subsingleton (ModuleH (residueAlgebraFiberLine q N w) (n + 1)) :=
    acyclic_pullback_positive (IsPullback.of_hasPullback q
      (AffineBaseChangeCoefficients.baseMap T w.asIdeal.ResidueField)) N hn hN n
  exact ⟨properLineRankOneOpen q N hn hv, hN, fun _ _ _ _ _ h ↦
    properLineRankOneOpen_represents q N hn hv h⟩

end FLT.Mazur.LineSectionBaseChange
