/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassSuccessiveRetainedCenter

/-!
# Regular generators and scale divisibility on retained equation charts

Flat presentations of either kind of retained x chart preserve a regular
principal generator of every deeper original center. The preceding output
scale belongs to that same principal ideal.
-/

@[expose] public noncomputable section
namespace FLT.Mazur.WeierstrassSuccessiveX
set_option backward.isDefEq.respectTransparency false
universe u
variable {R S : Type u} [CommRing R] [IsDomain R] [CommRing S]
  (W : WeierstrassCurve R) (s π b3 b4 b6 : R)

/-- Both the deeper center and its preceding scale share a regular original x generator. -/
theorem exteriorPresentation_regularCenter
    (h3 : W.a₃ = s * b3) (h4 : W.a₄ = s * b4) (h6 : W.a₆ = s ^ 2 * b6)
    (hs : s ≠ 0) (r : R)
    (ψ : WeierstrassModificationX.Coordinate W s b3 b4 b6 →+* S) (hψ : RingHom.Flat ψ) :
    ∃ x : S, IsRegular x ∧
      (WeierstrassIntegralChart.modificationChartCenter W ((s * r) * π) 2).map
        (ψ.comp (WeierstrassModificationX.fromOriginal W s b3 b4 b6 h3 h4 h6).toRingHom) =
          Ideal.span {x} ∧
      ψ (algebraMap R _ (s * r)) ∈ Ideal.span {x} := by
  refine ⟨ψ (WeierstrassModificationX.x W s b3 b4 b6),
    WeierstrassIntegralChart.flatRingHom_isRegular ψ hψ
      (WeierstrassModificationX.x_regular W s b3 b4 b6 hs), ?_, ?_⟩
  · rw [mul_assoc]
    exact originalDeeperCenter_map_exteriorPresentation W s (r * π) b3 b4 b6 h3 h4 h6 ψ
  · apply Ideal.mem_span_singleton.mpr
    refine ⟨ψ (WeierstrassModificationX.t W s b3 b4 b6 * algebraMap R _ r), ?_⟩
    rw [← map_mul]
    congr 1
    rw [map_mul, ← WeierstrassModificationX.incidence W s b3 b4 b6]
    ring

/-- Every retained successive x chart has a regular generator dividing all later scales. -/
theorem successivePresentation_regularCenter
    (h3 : W.a₃ = s * (π * b3)) (h4 : W.a₄ = s * (π * b4))
    (h6 : W.a₆ = s ^ 2 * (π ^ 2 * b6)) (hπ : π ≠ 0) (hs : s ≠ 0) (r : R)
    (ψ : Coordinate W s π b3 b4 b6 →+* S) (hψ : RingHom.Flat ψ) :
    ∃ x : S, IsRegular x ∧
      (WeierstrassIntegralChart.modificationChartCenter W ((s * (π * r)) * π) 2).map
        (ψ.comp ((fromDivided W s π b3 b4 b6).comp
          (WeierstrassDilatation.fromOriginal W s (π * b3) (π * b4) (π ^ 2 * b6)
            h3 h4 h6)).toRingHom) = Ideal.span {x} ∧
      ψ (algebraMap R _ (s * (π * r))) ∈ Ideal.span {x} := by
  refine ⟨ψ (algebraMap R _ s * coord W s π b3 b4 b6 2),
    originalHorizontalPresentation_regular W s π b3 b4 b6 hπ hs ψ hψ, ?_, ?_⟩
  · have he : s * (π * r) * π = s * (π * (r * π)) := by ring
    rw [he]
    exact originalDeeperCenter_map_successiveXPresentation W s π b3 b4 b6 h3 h4 h6 _ ψ
  · apply Ideal.mem_span_singleton.mpr
    refine ⟨ψ (coord W s π b3 b4 b6 0 * algebraMap R _ r), ?_⟩
    rw [← map_mul]
    congr 1
    simp only [map_mul]
    rw [← incidence W s π b3 b4 b6]
    ring

end FLT.Mazur.WeierstrassSuccessiveX
