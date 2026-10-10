/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialPrecedingExterior
public import FLT.Mazur.WeierstrassDividedAdjacentIntegralBoundary

/-!
# The original initial chart and first successive chart share their full boundary

The defining exterior pushout retains the complete original localization maps
at every later stage. This supplies the integral boundary for the first components.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (h1 : 1 ≤ n) (r : ℕ) (hr : 1 + r ≤ n)
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "e" => data (Fin.mk 1 (Nat.lt_succ_of_le h1))
local notation "E₀" => initialExterior d
local notation "tail" => finiteStageRetained hπ data 1 h1 r hr
local notation "ext" => Exterior.exteriorChart (finiteExterior hπ data E₀ (1 + r) hr)
local notation "i" => finiteInitialChart hπ data (1 + r) hr
local notation "l" => olderSuccessiveChart hπ data 0 h1 r hr

/-- Both original initial chart maps agree on the whole boundary after every retention. -/
@[reassoc] theorem initialRetainedIntegral_boundary :
    (E₀).attach ≫ i = previousToX hπ d e ≫ l := by
  rw [finiteInitialChart, finiteRetained_stage_factor hπ data 1 h1 r hr]
  change (E₀).attach ≫ ((𝟙 _ ≫ (E₀).retained hπ e) ≫ tail) ≫ ext =
    previousToX hπ d e ≫ (E₀).newX hπ e ≫ tail ≫ ext
  have H := pushout.condition_assoc (f := (E₀).attach)
    (g := previousToX hπ d e) (tail ≫ ext)
  simpa only [Category.id_comp, Category.assoc, Exterior.newX, Exterior.retained] using H

local notation "a" => WeierstrassModificationX.overlapEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "b" => previousBoundaryEquiv hπ d e
local notation "t" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "u" => WeierstrassSuccessiveX.coord W (π ^ start) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e) 2

omit [IsDomain R] in
/-- The original initial principal transition is the defining exterior attachment. -/
theorem initialExterior_attach_localization :
    (E₀).attach = Spec.map (CommRingCat.ofHom (AlgEquiv.symm a).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away t))) := by
  rfl

/-- Both full original localization maps agree before any contraction to the cubic. -/
@[reassoc] theorem initialRetainedIntegral_localizations :
    Spec.map (CommRingCat.ofHom (AlgEquiv.symm a).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away t))) ≫ i =
    Spec.map (CommRingCat.ofHom (AlgEquiv.symm b).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away u))) ≫ l := by
  rw [← Category.assoc]
  change (E₀).attach ≫ i = _
  exact (initialRetainedIntegral_boundary hπ data h1 r hr).trans
    (previousBoundary_inverse_inclusion_assoc hπ d e l).symm

end FLT.Mazur.WeierstrassDividedDepth
