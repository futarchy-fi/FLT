/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.PolygonCompleteIdentityActionNodeCover
public import FLT.Mazur.PolygonCompleteGenericMapIdentity

/-!
# Flatness and schematic density on the whole original action input

The smooth-second-input open is schematically dense in the original product.
This retains its full scheme structure when closing the constructed action graph.
-/

@[expose] public noncomputable section
open CategoryTheory Limits AlgebraicGeometry
namespace FLT.Mazur.PolygonInfinitesimalStages
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] exactVeroneseProj exactVeroneseProjToBase
attribute [local instance] exactVeroneseProjToBase_lfp
variable (K : Type) [Field K] (n : ℕ) (h : 2 ≤ n) [NeZero n]
local notation "G" => completePointOriginalBaseGroup K n h (0 : Fin n)
local notation "π" => exactVeroneseProjToBase K n h
local notation "P" => completeIdentityActionProduct K n h 0
local notation "s" => completeIdentityActionSecond K n h
local notation "V" => completeIdentityActionSmoothOpen K n h

/-- The original identity parameter remains flat over the literal power-series base. -/
theorem completeIdentityActionParameter_flat : Flat (G).X.hom := by
  rw [completePointOriginalBaseGroup_structure]
  let _ := exactVeroneseProjToBase_flat K n h
  infer_instance

/-- The entire action input product, including its node inputs, is flat over the base. -/
instance completeIdentityActionSource_flat : Flat ((s) ≫ (π)) := by
  let _ := completeIdentityActionParameter_flat K n h
  let _ := exactVeroneseProjToBase_flat K n h
  infer_instance

/-- The original whole action input is Noetherian. -/
instance completeIdentityActionSource_noetherian : IsNoetherian (P) := by
  let U := completePointIdentityOpen K n h (0 : Fin n)
  let _ : TopologicalSpace.NoetherianSpace U.toScheme :=
    TopologicalSpace.NoetherianSpace.set (U : Set (exactVeroneseProj K n h))
  let _ : QuasiCompact U.ι := quasiCompact_of_noetherianSpace_source _
  let _ : IsNoetherian (G).X.left := Chow.source_isNoetherian U.ι
  let _ := exactVeroneseProjToBase_isProper K n h
  exact Chow.source_isNoetherian (pullback.fst (G).X.hom (π))

/-- The full smooth input inclusion is quasi-compact without replacing its scheme structure. -/
instance completeIdentityActionSmooth_quasiCompact : QuasiCompact (V).ι := by
  let _ : TopologicalSpace.NoetherianSpace (V).toScheme :=
    TopologicalSpace.NoetherianSpace.set ((V) : Set (P))
  exact quasiCompact_of_noetherianSpace_source _

/-- The constructed smooth lift is defined on a schematically dense open of the whole input. -/
instance completeIdentityActionSmooth_schematic : IsSchemeTheoreticallyDominant (V).ι := by
  let L := FractionRing (PowerSeries K)
  let a := algebraMap (PowerSeries K) L
  have ha : a PowerSeries.X ≠ 0 := by
    intro hz
    exact PowerSeries.X_ne_zero ((IsFractionRing.injective (PowerSeries K) L)
      (hz.trans (map_zero a).symm))
  let b := Spec.map (CommRingCat.ofHom a)
  let r := pullback.fst ((s) ≫ (π)) b
  let q := pullback.snd ((s) ≫ (π)) b
  have hr := completeGenericMap_preimage_identity K n h 0 L a ha (r ≫ (s)) q
    (by simpa only [Category.assoc] using
      pullback.condition (f := (s) ≫ (π)) (g := b))
  let l : pullback ((s) ≫ (π)) b ⟶ (V).toScheme :=
    IsOpenImmersion.lift (V).ι r (by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨x, rfl⟩
      exact completePointIdentityOpen_le_smooth K n h 0
        (hr.ge (show x ∈ ⊤ from trivial)))
  have hl : l ≫ (V).ι = r := IsOpenImmersion.lift_fac _ _ _
  let _ := completeFlat_generic_dense K L ((s) ≫ (π))
  constructor
  apply le_bot_iff.mp
  calc
    (V).ι.ker ≤ (l ≫ (V).ι).ker := l.le_ker_comp _
    _ = r.ker := congrArg Scheme.Hom.ker hl
    _ = ⊥ := r.ker_eq_bot

/-- Every original input is in the closure of the actual smooth-lift domain. -/
theorem completeIdentityActionSmooth_dense :
    Dense (completeIdentityActionSmoothOpen K n h : Set (P)) := by
  rw [← Scheme.Opens.range_ι]
  exact (V).ι.denseRange

end FLT.Mazur.PolygonInfinitesimalStages
