/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveXDeeperCenter

/-!
# Cancelling retained successive x-chart generators in deeper output centers

Original-center invariance and the actual coefficient agreement force a
unit successive output center whenever the input is an older successive
x chart. Flatness preserves the regular original horizontal generator.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
variable {R : Type*} [CommRing R] [IsDomain R]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)
  (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
  (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6)) (hπ : π ≠ 0) (hs : s ≠ 0)
  (r c3 c4 c6 : R)
  (g3 : W.a₃ = (s * (π * r)) * (π * c3))
  (g4 : W.a₄ = (s * (π * r)) * (π * c4))
  (g6 : W.a₆ = (s * (π * r)) ^ 2 * (π ^ 2 * c6))
local notation "A" => Coordinate W s π b3 b4 b6
local notation "T" => coord W s π b3 b4 b6 0
local notation "U" => coord W s π b3 b4 b6 2
local notation "t" => s * (π * r)
local notation "B" => WeierstrassDilatation.Coordinate W t (π * c3) (π * c4) (π ^ 2 * c6)
local notation "c" => AlgHom.comp (fromDivided W s π b3 b4 b6)
  (WeierstrassDilatation.fromOriginal W s (π * b3) (π * b4) (π ^ 2 * b6) h3 h4 h6)
local notation "q" => WeierstrassDilatation.fromOriginal W t
  (π * c3) (π * c4) (π ^ 2 * c6) g3 g4 g6

include hπ hs
/-- A flat retained successive input and original-center invariance give a unit output center. -/
theorem successiveCenter_unit_of_retainedPresentation {S : Type*} [CommRing S]
    (α : B →+* S) (ψ : A →+* S) (hψ : RingHom.Flat ψ)
    (hc : α.comp (algebraMap R B) = ψ.comp (algebraMap R A))
    (he : (WeierstrassIntegralChart.modificationChartCenter W (t * π) 2).map
        (α.comp (q).toRingHom) =
      (WeierstrassIntegralChart.modificationChartCenter W (t * π) 2).map
        (ψ.comp (c).toRingHom)) :
    (modificationCenter W t π c3 c4 c6).map α = ⊤ := by
  rw [← Ideal.map_map, originalCenter_map_fromOriginal, Ideal.map_mul, Ideal.map_span] at he
  simp only [Set.image_singleton] at he
  have hscale : t * π = s * (π * (r * π)) := by ring
  have hin : (WeierstrassIntegralChart.modificationChartCenter W (t * π) 2).map
      (ψ.comp (c).toRingHom) = Ideal.span {ψ (algebraMap R A s * U)} := by
    rw [hscale]
    exact originalDeeperCenter_map_successiveXPresentation W s π b3 b4 b6 h3 h4 h6 _ ψ
  rw [hin] at he
  have hc' : α (algebraMap R B t) =
      ψ (algebraMap R A s * U) * ψ (T * algebraMap R A r) := by
    calc
      _ = ψ (algebraMap R A t) := RingHom.congr_fun hc t
      _ = ψ ((algebraMap R A s * U) * (T * algebraMap R A r)) := by
        congr 1
        rw [map_mul, map_mul, ← incidence W s π b3 b4 b6]
        ring
      _ = _ := map_mul ψ _ _
  rw [hc'] at he
  exact successiveCenter_unit_of_scaled_eq _ _ _
    (originalHorizontalPresentation_regular W s π b3 b4 b6 hπ hs ψ hψ) he

end FLT.Mazur.WeierstrassSuccessiveX
