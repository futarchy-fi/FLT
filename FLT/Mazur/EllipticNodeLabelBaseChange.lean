/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticComponentBaseChange
public import FLT.Mazur.EllipticNodeComponentBound

/-!
# Nodal labels under compatible local base change

Primitive nodal coordinates extend along compatible field and valuation-ring
maps. When the uniformizer and exact split depth are preserved, both the actual
point labels and their component-quotient labels are unchanged.
-/

set_option backward.isDefEq.respectTransparency false

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K L : Type*} [Field K] [Field L]
  (A : ValuationSubring K) (B : ValuationSubring L) (W : WeierstrassCurve A)
  (f : K →+* L) (g : A →+* B)
  (hc : (algebraMap B L).comp g = f.comp (algebraMap A K))

/-- Primitive scaled coordinates extend with the same common exponent. -/
def NodePointCoordinates.extension {π : A}
    {P : (W.map (algebraMap A K)).toProjective.Point}
    (v : NodePointCoordinates A W π P) :
    NodePointCoordinates B (W.map g) (g π) (integralProjectiveExtension A B W f g hc P) := by
  have he : (W.map g).map (algebraMap B L) = (W.map (algebraMap A K)).map f := by
    rw [map_map, map_map, hc]
  have hxy (a : A) : ((g π ^ v.depth * g a : B) : L) = f ((π ^ v.depth * a : A) : K) := by
    rw [← map_pow, ← map_mul]
    exact RingHom.congr_fun hc _
  have hs : ((W.map g).map (algebraMap B L)).toAffine.Nonsingular
      ((g π ^ v.depth * g v.a : B) : L) ((g π ^ v.depth * g v.b : B) : L) := by
    rw [he, hxy, hxy]
    exact ((W.map (algebraMap A K)).toAffine.map_nonsingular f.injective _ _).mpr
      v.nonsingular
  refine ⟨v.depth, g v.a, g v.b, v.primitive.imp (fun h => h.map g) (fun h => h.map g), hs, ?_⟩
  apply Point.ext
  conv_lhs => rw [v.represents]
  change (⟦f ∘ ![((π ^ v.depth * v.a : A) : K), ((π ^ v.depth * v.b : A) : K), 1]⟧ :
      PointClass L) = ⟦![((g π ^ v.depth * g v.a : B) : L),
        ((g π ^ v.depth * g v.b : B) : L), 1]⟧
  rw [comp_fin3, map_one, hxy, hxy]

variable [IsLocalHom g]

/-- Local coefficient maps preserve signed branch labels. -/
theorem nodeBranchLabel_map (n k : ℕ) (b : A) :
    nodeBranchLabel n k (g b) = nodeBranchLabel n k b := by
  have hm : g b ∈ maximalIdeal B ↔ b ∈ maximalIdeal A := by
    change b ∈ (maximalIdeal B).comap g ↔ _
    rw [maximalIdeal_comap]
  unfold nodeBranchLabel
  congr 1
  exact propext (or_congr Iff.rfl hm)

/-- The actual point label is functorial when exact depth and uniformizer are preserved. -/
theorem nodePointLabel_integralProjectiveExtension {π : A} {n : ℕ}
    (D : SplitNodeDepth W π n) (D' : SplitNodeDepth (W.map g) (g π) n)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D' (integralProjectiveExtension A B W f g hc P) = nodePointLabel D P := by
  by_cases hp : SmoothReduction A W P
  · rw [(nodePointLabel_eq_zero_iff D P).mpr hp,
      (nodePointLabel_eq_zero_iff D' _).mpr
        ((smoothReduction_integralProjectiveExtension A B W f g hc P).mpr hp)]
  · obtain ⟨v, _⟩ := exists_nodePointCoordinates A W π D.maximalIdeal_eq n
      D.a₃_mem D.a₄_mem D.a₆_not_mem P hp
    rw [nodePointLabel_eq_of_coordinates D v,
      nodePointLabel_eq_of_coordinates D' (v.extension A B W f g hc)]
    exact nodeBranchLabel_map A B g n v.depth v.b

/-- Point-label functoriality with an explicitly identified target equation. -/
theorem nodePointLabel_extensionProjectiveHom {π : A} {n : ℕ}
    (D : SplitNodeDepth W π n) {V : WeierstrassCurve B}
    (D' : SplitNodeDepth V (g π) n) (he : W.map g = V)
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    nodePointLabel D' (extensionProjectiveHom _ f (V.map (algebraMap B L))
      (by rw [← he, map_map, map_map, hc]) P) = nodePointLabel D P := by
  subst V
  exact nodePointLabel_integralProjectiveExtension A B W f g hc D D' P

/-- The comparison of actual component classes preserves their nodal labels. -/
theorem nodeComponentLabel_integralComponentExtension {π : A} {n : ℕ}
    (D : SplitNodeDepth W π n) (D' : SplitNodeDepth (W.map g) (g π) n)
    (c : EllipticComponentQuotient A W) :
    nodeComponentLabel D' (integralComponentExtension A B W f g hc c) =
      nodeComponentLabel D c := by
  obtain ⟨P, rfl⟩ := ellipticComponentHom_surjective A W c
  rw [integralComponentExtension_mk, nodeComponentLabel_mk, nodeComponentLabel_mk]
  exact nodePointLabel_integralProjectiveExtension A B W f g hc D D' P

end FLT.Mazur
