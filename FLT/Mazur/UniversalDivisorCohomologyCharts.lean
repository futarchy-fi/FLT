/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalDivisorTwistedLine
public import FLT.Mazur.ProperLinePrincipalRankOne

/-!
# Actual universal-divisor cohomology opens on parameter charts

Apply the varying-line vanishing theorem to the full universal divisor
bundle, with an arbitrary original line twist. No vanishing of this varying
line is assumed globally. One acyclic fiber gives universal acyclicity on
a principal neighborhood, even after nonflat coefficient base change.
-/

@[expose] public noncomputable section
open CategoryTheory AlgebraicGeometry
open Scheme.Modules
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
namespace FLT.Mazur.ProperUniversalDirectImage
open FCurve LineSectionBaseChange LocallyFreeDualProjectiveAtlas
attribute [local irreducible] ModuleSheafTensor.tensor
attribute [local irreducible] LocallyFreeDualProjectiveAtlas.space
  LocallyFreeDualProjectiveAtlas.projection
variable {X S : Scheme.{0}} [IsAffine S] [IsNoetherianRing Γ(S, ⊤)]
  (f : X ⟶ S) [IsProper f] [Flat f] [GeometricallyIntegral f]
  (L : X.Modules) (hL : LocallyFreeRankOne L)
  (hV : ∀ (z : PrimeSpectrum Γ(S, ⊤)) n,
    Subsingleton (ModuleH (residueAlgebraFiberLine f L z) (n + 1)))

local notation "M" => Functor.obj (pushforward f) L
local notation "hM" => properLinePushforward_locallyFiniteFree f L hL hV
local notation "π" => projection M hM
local notation "q" => Limits.pullback.snd f π
variable (K : X.Modules) (hK : LocallyFreeRankOne K)
  (chart : (space ((pushforward f).obj L)
    (properLinePushforward_locallyFiniteFree f L hL hV)).affineOpens)
local notation "N" => divisorTwistedChartLine f L hL hV K chart
local notation "hN" => divisorTwistedChartLine_rankOne f L hL hV K hK chart

omit [GeometricallyIntegral f] in
include f L hL hV in
/-- Every actual affine chart of the universal parameter atlas has Noetherian coefficients. -/
theorem universalChart_noetherian : IsNoetherianRing Γ(chart.1.toScheme, ⊤) := by
  let _ := atlas_locallyNoetherian f L hL hV
  exact IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top chart.1.toScheme⟩

/-- The cohomology open for the actual varying universal-divisor line in an atlas chart. -/
def divisorAcyclicChartOpen : chart.1.toScheme.Opens := by
  let _ := universalChart_noetherian f L hL hV chart
  exact properLineAcyclicOpen (q ∣_ chart.1) N hN

/-- Membership tests the actual residue-fiber cohomology of the universal-divisor line. -/
lemma mem_divisorAcyclicChartOpen (u : chart.1.toScheme) :
    u ∈ divisorAcyclicChartOpen f L hL hV K hK chart ↔ ∀ n,
      Subsingleton (ModuleH (residueAlgebraFiberLine (q ∣_ chart.1) N
        (chart.1.toScheme.isoSpec.hom u)) (n + 1)) := Iff.rfl

include hK in
/-- Acyclic universal-divisor fibers construct principal universally acyclic neighborhoods. -/
theorem divisorChart_exists_universal_acyclic
    (z : PrimeSpectrum Γ(chart.1.toScheme, ⊤))
    (hz : ∀ n, Subsingleton (ModuleH (residueAlgebraFiberLine (q ∣_ chart.1) N z) (n + 1))) :
    ∃ r ∉ z.asIdeal, ∀ (B : Type) [CommRing B] [Algebra Γ(chart.1.toScheme, ⊤) B]
      [Algebra (Localization.Away r) B]
      [IsScalarTower Γ(chart.1.toScheme, ⊤) (Localization.Away r) B],
      ∀ n, Subsingleton (ModuleH
        ((pullback (Limits.pullback.fst (q ∣_ chart.1)
          (AffineBaseChangeCoefficients.baseMap chart.1.toScheme B))).obj N) (n + 1)) := by
  let _ := universalChart_noetherian f L hL hV chart
  exact exists_principal_universal_positive_vanishing (q ∣_ chart.1) N hN z hz

include hK in
/-- The actual varying-divisor family has principal rank-one representing opens near acyclicity. -/
theorem divisorChart_exists_rankOne_open
    (z : PrimeSpectrum Γ(chart.1.toScheme, ⊤))
    (hz : ∀ n, Subsingleton (ModuleH (residueAlgebraFiberLine (q ∣_ chart.1) N z) (n + 1))) :
    ∃ r ∉ z.asIdeal,
      let g := AffineBaseChangeCoefficients.baseMap chart.1.toScheme (Localization.Away r)
      let a := Limits.pullback.fst (q ∣_ chart.1) g
      let b := Limits.pullback.snd (q ∣_ chart.1) g
      let E := (pullback a).obj N
      ∃ V : (Spec (.of (Localization.Away r))).Opens,
        (∀ n, Subsingleton (ModuleH E (n + 1))) ∧
        ∀ (P T : Scheme.{0}) (i : P ⟶ Limits.pullback (q ∣_ chart.1) g) (j : P ⟶ T)
          (k : T ⟶ Spec (.of (Localization.Away r))), IsPullback i j b k →
          (LocallyFreeRankOne ((pushforward j).obj ((pullback i).obj E)) ↔
            ∃! t : T ⟶ V.toScheme, t ≫ V.ι = k) := by
  let _ := universalChart_noetherian f L hL hV chart
  exact exists_principal_rankOne_representing_open (q ∣_ chart.1) N hN z hz

end FLT.Mazur.ProperUniversalDirectImage
