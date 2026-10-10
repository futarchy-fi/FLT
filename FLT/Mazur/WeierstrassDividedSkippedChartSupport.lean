/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedOppositeBoundarySupport

/-!
# A skipped successive chart can intersect only away from the special fiber

An exterior preceding one full intervening chart meets the next chart only
where π is nonzero. The statement survives every later monomorphic retention.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type*} [CommRing R] [IsDomain R] {W : WeierstrassCurve R} {π : R}
  (hπ : π ≠ 0) {k : ℕ} {d : Data W π k} (E : Exterior d)
  (e : Data W π (k + 1)) (f : Data W π (k + 1 + 1))
local notation "E₁" => Exterior.advance hπ E e
local notation "E₂" => Exterior.advance hπ E₁ f
local notation "T" => WeierstrassSuccessiveX.Coordinate W (π ^ k) π
  (Data.b3 e) (Data.b4 e) (Data.b6 e)

/-- An intersection with the older exterior passes through both opposite middle boundaries. -/
theorem Exterior.skipped_intersection_lift (a : E.carrier) (c : stepX f)
    (h : (E₁).retained hπ f (E.retained hπ e a) = (E₁).newX hπ f c) :
    ∃ b : boundary e,
      (E₁).attach b = E.retained hπ e a ∧ previousToX hπ e f b = c ∧
        nextToX e b ∈ Set.range (previousToX hπ d e) := by
  obtain ⟨b, hb, hc⟩ := Scheme.exists_preimage_of_isPullback
    ((E₁).retained_newX_isPullback hπ f) (E.retained hπ e a) c h
  refine ⟨b, hb, hc, ?_⟩
  rw [← E.newX_retained_preimage hπ e]
  exact ⟨a, hb.symm⟩

variable {X : Scheme}
  (tail : ((E.advance hπ e).advance hπ f).carrier ⟶ X) [IsOpenImmersion tail]
  (base : X ⟶ Spec (.of R))
  (hbase : E.newX hπ e ≫ (E.advance hπ e).retained hπ f ≫ tail ≫ base =
    Spec.map (CommRingCat.ofHom (algebraMap R
      (WeierstrassSuccessiveX.Coordinate W (π ^ k) π e.b3 e.b4 e.b6))))

include hbase in
/-- No special-fiber point belongs to both a skipped exterior and the new chart. -/
theorem Exterior.skipped_intersection_parameter_notMem (a : E.carrier) (c : stepX f)
    (h : (E.retained hπ e ≫ (E₁).retained hπ f ≫ tail) a =
      ((E₁).newX hπ f ≫ tail) c) :
    π ∉ (base (((E₁).newX hπ f ≫ tail) c)).asIdeal := by
  have h' : (E₁).retained hπ f (E.retained hπ e a) = (E₁).newX hπ f c :=
    tail.isOpenEmbedding.injective h
  obtain ⟨b, hb, hc, hp⟩ := E.skipped_intersection_lift hπ e f a c h'
  have hn := oppositeBoundary_parameter_notMem hπ d e (nextToX e b) ⟨b, rfl⟩ hp
  have hm : (E.newX hπ e ≫ (E₁).retained hπ f ≫ tail ≫ base) (nextToX e b) =
      base (((E₁).newX hπ f ≫ tail) c) := by
    change base (tail ((E₁).retained hπ f ((E₁).attach b))) = _
    rw [hb, h']
    rfl
  rw [hbase] at hm
  rw [← hm]
  exact hn

end FLT.Mazur.WeierstrassDividedDepth
