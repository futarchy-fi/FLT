/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalDivisorGlobalCohomology
public import FLT.Mazur.ProperAcyclicRankOneLocus

/-!
# The actual universal-divisor acyclic rank-one open

The varying universal-divisor line determines an intrinsic open where its
fibers have H0 dimension one and no positive cohomology. This is an open of
the existing projective atlas, not a Picard representing scheme.
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


/-- The actual simultaneous cohomology and section-rank open in the original parameter atlas. -/
def divisorAcyclicRankOneOpen : (space M hM).Opens := by
  let _ := atlas_locallyNoetherian f L hL hV
  exact properLineAcyclicRankOneOpen q (divisorTwistedLine f L hL hV K)
    (divisorTwistedLine_rankOne f L hL hV K hK)

/-- The open tests precisely the original universal family's two cohomology conditions. -/
theorem mem_divisorAcyclicRankOneOpen (s : space M hM) :
    s ∈ divisorAcyclicRankOneOpen f L hL hV K hK ↔
      s ∈ divisorAcyclicOpen f L hL hV K hK ∧
        properLineFiberSectionRank q (divisorTwistedLine f L hL hV K) s = 1 := by
  let _ := atlas_locallyNoetherian f L hL hV
  exact mem_properLineAcyclicRankOneOpen q (divisorTwistedLine f L hL hV K)
    (divisorTwistedLine_rankOne f L hL hV K hK) s

/-- Unrestricted test families factor uniquely exactly when both actual fiber conditions hold. -/
theorem divisorAcyclicRankOneOpen_represents {P T : Scheme.{0}}
    {a : P ⟶ Limits.pullback f π} {b : P ⟶ T} {g : T ⟶ space M hM}
    (h : IsPullback a b q g) :
    (∀ t : T, (∀ n, Subsingleton (ModuleH ((pullback (b.fiberι t)).obj
      ((pullback a).obj (divisorTwistedLine f L hL hV K))) (n + 1))) ∧
        properLineFiberSectionRank b
          ((pullback a).obj (divisorTwistedLine f L hL hV K)) t = 1) ↔
      ∃! u : T ⟶ (divisorAcyclicRankOneOpen f L hL hV K hK).toScheme,
        u ≫ (divisorAcyclicRankOneOpen f L hL hV K hK).ι = g := by
  let _ := atlas_locallyNoetherian f L hL hV
  exact properLineAcyclicRankOneOpen_represents q (divisorTwistedLine f L hL hV K)
    (divisorTwistedLine_rankOne f L hL hV K hK) h

variable (chart : (space ((pushforward f).obj L)
  (properLinePushforward_locallyFiniteFree f L hL hV)).affineOpens)

/-- The simultaneous open constructed independently in an actual affine parameter chart. -/
def divisorAcyclicRankOneChartOpen : chart.1.toScheme.Opens := by
  let _ := atlas_locallyNoetherian f L hL hV
  exact properLineAcyclicRankOneOpen (q ∣_ chart.1)
    (divisorTwistedChartLine f L hL hV K chart)
    (divisorTwistedChartLine_rankOne f L hL hV K hK chart)

/-- The independent simultaneous chart opens are restrictions of the single global open. -/
theorem divisorAcyclicRankOneChartOpen_eq_preimage :
    divisorAcyclicRankOneChartOpen f L hL hV K hK chart =
      chart.1.ι ⁻¹ᵁ divisorAcyclicRankOneOpen f L hL hV K hK := by
  let _ := atlas_locallyNoetherian f L hL hV
  let E := divisorTwistedLine f L hL hV K
  have hE := divisorTwistedLine_rankOne f L hL hV K hK
  have he : divisorTwistedChartLine f L hL hV K chart =
      (pullback (q ⁻¹ᵁ chart.1).ι).obj E := by
    rw [divisorTwistedChartLine]
  change properLineAcyclicRankOneOpen (q ∣_ chart.1)
    (divisorTwistedChartLine f L hL hV K chart) _ = _
  simp only [he]
  exact properLineAcyclicRankOneOpen_baseChange q E hE
    (isPullback_morphismRestrict q chart.1).flip

/-- All common refinements retain identical simultaneous cohomology and rank-one opens. -/
theorem divisorAcyclicRankOneChartOpen_overlap
    (other : (space M hM).affineOpens) {T : Scheme.{0}}
    (a : T ⟶ chart.1.toScheme) (b : T ⟶ other.1.toScheme)
    (hab : a ≫ chart.1.ι = b ≫ other.1.ι) :
    a ⁻¹ᵁ divisorAcyclicRankOneChartOpen f L hL hV K hK chart =
      b ⁻¹ᵁ divisorAcyclicRankOneChartOpen f L hL hV K hK other := by
  rw [divisorAcyclicRankOneChartOpen_eq_preimage, divisorAcyclicRankOneChartOpen_eq_preimage,
    ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hab]

end FLT.Mazur.ProperUniversalDirectImage
