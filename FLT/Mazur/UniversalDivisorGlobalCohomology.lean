/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.UniversalDivisorCohomologyCharts
public import FLT.Mazur.ProperLineGlobalAcyclicOpen

/-!
# The global universal-divisor cohomology open and its overlaps

The varying full universal-divisor line has a single intrinsic cohomology
open on the original projective atlas. Every affine chart construction is
its exact inverse image; arbitrary common refinements therefore agree.
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

/-- The intrinsic global acyclic open for the actual varying universal-divisor line. -/
def divisorAcyclicOpen : (space M hM).Opens := by
  let _ := atlas_locallyNoetherian f L hL hV
  exact properLineGlobalAcyclicOpen q (divisorTwistedLine f L hL hV K)
    (divisorTwistedLine_rankOne f L hL hV K hK)

/-- The assembled locus tests the original universal family's actual residue fibers. -/
lemma mem_divisorAcyclicOpen (s : space M hM) :
    s ∈ divisorAcyclicOpen f L hL hV K hK ↔ ∀ n,
      Subsingleton (ModuleH ((pullback ((q).fiberι s)).obj
        (divisorTwistedLine f L hL hV K)) (n + 1)) := Iff.rfl

/-- Each previously constructed affine-chart open is exactly the global open's inverse image. -/
theorem divisorAcyclicChartOpen_eq_preimage :
    divisorAcyclicChartOpen f L hL hV K hK chart =
      chart.1.ι ⁻¹ᵁ divisorAcyclicOpen f L hL hV K hK := by
  let _ := atlas_locallyNoetherian f L hL hV
  let _ := universalChart_noetherian f L hL hV chart
  let E := divisorTwistedLine f L hL hV K
  have hE := divisorTwistedLine_rankOne f L hL hV K hK
  have he : divisorTwistedChartLine f L hL hV K chart =
      (pullback (q ⁻¹ᵁ chart.1).ι).obj E := by
    rw [divisorTwistedChartLine]
  change properLineAcyclicOpen (q ∣_ chart.1)
    (divisorTwistedChartLine f L hL hV K chart) _ = _
  simp only [he]
  exact (properLineGlobalAcyclicOpen_eq_affine (q ∣_ chart.1)
    ((pullback (q ⁻¹ᵁ chart.1).ι).obj E) (hE.pullback _)).symm.trans
      (properLineGlobalAcyclicOpen_restrict q E hE chart.1)

/-- Any common refinement of two original affine charts has identical cohomology opens. -/
theorem divisorAcyclicChartOpen_overlap
    (other : (space M hM).affineOpens) {T : Scheme.{0}}
    (a : T ⟶ chart.1.toScheme) (b : T ⟶ other.1.toScheme)
    (hab : a ≫ chart.1.ι = b ≫ other.1.ι) :
    a ⁻¹ᵁ divisorAcyclicChartOpen f L hL hV K hK chart =
      b ⁻¹ᵁ divisorAcyclicChartOpen f L hL hV K hK other := by
  rw [divisorAcyclicChartOpen_eq_preimage, divisorAcyclicChartOpen_eq_preimage,
    ← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, hab]

end FLT.Mazur.ProperUniversalDirectImage
