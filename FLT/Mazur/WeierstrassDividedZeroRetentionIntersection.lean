/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialTensorChart
public import FLT.Mazur.WeierstrassModificationChartIntersection
public import FLT.Mazur.TensorOpenChartIntersection

/-!
# The initial/terminal intersection at zero retention

Before any successive modification, the initial and terminal charts meet
along the original modification overlap. This intersection is not an
instance of the positive-retention nonadjacency exclusion.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "E" => initialExterior d
local notation "x" => WeierstrassDilatation.x W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "t" => WeierstrassModificationX.t W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "a" => WeierstrassModificationX.overlapEquiv W (π ^ start)
  (Data.b3 d) (Data.b4 d) (Data.b6 d)
local notation "D" => Exterior.dividedChart (finiteExterior hπ data E 0 (Nat.zero_le n))
local notation "I" => finiteInitialChart hπ data 0 (Nat.zero_le n)

/-- The zero-retention initial chart is the original initial exterior map. -/
theorem finiteInitialChart_zero_eq_exterior : I = (E).exteriorChart := by
  change (𝟙 _) ≫ (E).exteriorChart = (E).exteriorChart
  exact Category.id_comp _

/-- The full original modification overlap commutes in the zero-retention finite model. -/
theorem zeroRetentionIntegral_overlap :
    Spec.map (CommRingCat.ofHom (a).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away x))) ≫ D =
        Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away t))) ≫ I := by
  rw [finiteInitialChart_zero_eq_exterior]
  apply (cancel_mono (initialExteriorIso d).hom).mp
  change (WeierstrassModificationX.overlapToDivided W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d) ≫ (E).dividedChart) ≫ _ = _
  simp only [Category.assoc, initialExteriorIso_divided, initialExteriorIso_exterior]
  exact (WeierstrassModificationX.chart_overlap W (π ^ start)
    (Data.b3 d) (Data.b4 d) (Data.b6 d)).symm

/-- At zero retention the initial preimage of the divided chart is the whole incidence open. -/
theorem zeroRetentionIntegral_preimage :
    I ⁻¹' Set.range D =
      Set.range (Spec.map (CommRingCat.ofHom (algebraMap _ (Localization.Away t)))) := by
  rw [finiteInitialChart_zero_eq_exterior]
  ext z
  constructor
  · rintro ⟨y, hy⟩
    have he := congrArg (initialExteriorIso d).hom hy
    change ((E).dividedChart ≫ (initialExteriorIso d).hom) y =
      ((E).exteriorChart ≫ (initialExteriorIso d).hom) z at he
    rw [initialExteriorIso_divided, initialExteriorIso_exterior] at he
    obtain ⟨w, hw, _⟩ := (WeierstrassModificationX.xChart_eq_dividedChart_iff
      W (π ^ start) (Data.b3 d) (Data.b4 d) (Data.b6 d) z y).mp he.symm
    exact ⟨w, hw⟩
  · rintro ⟨w, rfl⟩
    refine ⟨WeierstrassModificationX.overlapToDivided W (π ^ start)
      (Data.b3 d) (Data.b4 d) (Data.b6 d) w, ?_⟩
    exact congrArg (fun f => f w) (zeroRetentionIntegral_overlap hπ data)

variable (S : Type u) [CommRing S] [Algebra R S]

/-- The complete zero-retention tensor overlap is the actual initial/terminal fiber product. -/
theorem zeroRetentionFiniteTensor_isPullback :
    IsPullback ((PrincipalOpenTensor.transitionIso S x t a).hom ≫
      PrincipalOpenTensor.inclusion S x) (PrincipalOpenTensor.inclusion S t)
      (finiteDividedTensorChart hπ data S 0 (Nat.zero_le n))
      (finiteInitialTensorChart hπ data S 0 (Nat.zero_le n)) :=
  TensorOpenChart.chart_overlap_isPullback S _ _ _ _ _ x t a
    (zeroRetentionIntegral_overlap hπ data) (zeroRetentionIntegral_preimage hπ data)

end FLT.Mazur.WeierstrassDividedDepth
