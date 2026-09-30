/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.ClosedLineProjectionFormula
public import FLT.Mazur.ClosedPushforwardCohomology
public import FLT.Mazur.ModuleLineBundleTensorPullback
public import FLT.Mazur.ProjectiveSerreVanishing

/-!
# Serre vanishing on closed subschemes of projective space

The canonical line projection formula transports absolute Serre vanishing to
any coherent coefficient on a closed subscheme, with one bound for all positive
cohomological degrees.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.Scheme.Modules
open FLT.Mazur.FCurve

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

/-- Tensoring a coherent module by a locally free rank-one module preserves coherence. -/
lemma tensor_line_isFinitePresentation {X : Scheme.{u}} (F L : X.Modules)
    [F.IsFinitePresentation] (hL : LocallyFreeRankOne L) :
    (ModuleSheafTensor.tensor F L).IsFinitePresentation := by
  choose U hx e using hL
  apply coherent_of_openCover _ U
  · apply top_unique
    intro x _
    exact Opens.mem_iSup.mpr ⟨x, hx x⟩
  · intro x
    exact (SheafOfModules.isFinitePresentation (U x).toScheme.ringCatSheaf).prop_of_iso
      (ModuleSheafTensor.restrictIso F L (U x).ι ≪≫
        ModuleSheafTensor.rightTrivialIso (F.restrict (U x).ι) (e x).some).symm
      (coherent_restrict (U x).ι F)

end FLT.Mazur.FCurve

namespace FLT.Mazur.ProjectiveSpace

variable (R : Type u) [CommRing R] [IsNoetherianRing R] (ι : Type u) [Finite ι]

/-- One bound kills all positive cohomology of twists on a closed projective subscheme. -/
theorem exists_closed_twist_moduleH_subsingleton {Y : Scheme.{u}}
    (i : Y ⟶ space R ι) [IsClosedImmersion i] (F : Y.Modules) [F.IsFinitePresentation] :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (ModuleSheafTensor.tensor F
        ((pullback i).obj (twistingSheaf R ι (n : ℤ)))) (q + 1)) := by
  let : ((pushforward i).obj F).IsFinitePresentation :=
    CoherentDevissage.closedPushforward_isFinitePresentation i F
  obtain ⟨N, hN⟩ := exists_twistTensor_moduleH_subsingleton R ι ((pushforward i).obj F)
  refine ⟨N, fun n hn q ↦ ?_⟩
  let L := twistingSheaf R ι (n : ℤ)
  have hL : LocallyFreeRankOne L := twistingSheaf_locallyFreeRankOne R ι (n : ℤ)
  let M := ModuleSheafTensor.tensor F ((pullback i).obj L)
  let : M.IsFinitePresentation := tensor_line_isFinitePresentation F _ (hL.pullback i)
  let : Subsingleton (ModuleH ((pushforward i).obj M) (q + 1)) :=
    @moduleH_subsingleton_of_iso (space R ι) _ _
      (ClosedLineProjectionFormula.projectionIso i F L hL) (q + 1) (hN n hn q)
  exact (closedPushforwardModuleHEquiv i M (q + 1)).symm.toEquiv.injective.subsingleton

/-- Natural powers of `O(1)` identify with the integer twisting sheaves, including zero. -/
def twistingSheafPowerIso : ∀ n : ℕ,
    ModuleLineBundleTensorPullback.tensorPower (twistingSheaf R ι 1) n ≅
      twistingSheaf R ι (n : ℤ)
  | 0 => (twistingSheafZeroIso R ι).symm
  | n + 1 => ModuleSheafTensor.congr (Iso.refl _) (twistingSheafPowerIso n) ≪≫
      twistingSheafTensorIso R ι 1 (n : ℤ) ≪≫
        eqToIso (by congr 1; omega)

/-- Pullback identifies every projective twist with the corresponding actual line power. -/
def closedTwistPowerIso {Y : Scheme.{u}} (i : Y ⟶ space R ι) (n : ℕ) :
    (pullback i).obj (twistingSheaf R ι (n : ℤ)) ≅
      ModuleLineBundleTensorPullback.tensorPower ((pullback i).obj
        (twistingSheaf R ι 1)) n :=
  (pullback i).mapIso (twistingSheafPowerIso R ι n).symm ≪≫
    ModuleLineBundleTensorPullback.tensorPowerIso i (twistingSheaf R ι 1) n

/-- Serre vanishing for actual tensor powers of the pulled-back projective line sheaf. -/
theorem exists_closed_line_power_moduleH_subsingleton {Y : Scheme.{u}}
    (i : Y ⟶ space R ι) [IsClosedImmersion i] :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (ModuleLineBundleTensorPullback.tensorPower
        ((pullback i).obj (twistingSheaf R ι 1)) n) (q + 1)) := by
  let : (structureModule Y).IsFinitePresentation := unitSheaf_isFinitePresentation Y
  obtain ⟨N, hN⟩ := exists_closed_twist_moduleH_subsingleton R ι i (structureModule Y)
  refine ⟨N, fun n hn q ↦ ?_⟩
  exact @moduleH_subsingleton_of_iso Y _ _
    ((closedTwistPowerIso R ι i n).symm ≪≫ (ModuleSheafTensor.leftUnitor _).symm)
      (q + 1) (hN n hn q)

/-- Tensor powers respect an actual isomorphism of line coefficients. -/
def lineTensorPowerIso {Y : Scheme.{u}} {L M : Y.Modules} (e : L ≅ M) :
    ∀ n : ℕ, ModuleLineBundleTensorPullback.tensorPower L n ≅
      ModuleLineBundleTensorPullback.tensorPower M n
  | 0 => Iso.refl _
  | n + 1 => ModuleSheafTensor.congr e (lineTensorPowerIso e n)

/-- The same vanishing applies to a specified line identified by a projective embedding. -/
theorem exists_line_power_moduleH_subsingleton_of_projective_embedding {Y : Scheme.{u}}
    (i : Y ⟶ space R ι) [IsClosedImmersion i] (L : Y.Modules)
    (e : L ≅ (pullback i).obj (twistingSheaf R ι 1)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ q : ℕ,
      Subsingleton (ModuleH (ModuleLineBundleTensorPullback.tensorPower L n) (q + 1)) := by
  obtain ⟨N, hN⟩ := exists_closed_line_power_moduleH_subsingleton R ι i
  refine ⟨N, fun n hn q ↦ ?_⟩
  let := hN n hn q
  exact moduleH_subsingleton_of_iso (lineTensorPowerIso e n) (q + 1)

end FLT.Mazur.ProjectiveSpace
