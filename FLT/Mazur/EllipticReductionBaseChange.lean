/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.EllipticProjectiveBaseChange
public import FLT.Mazur.EllipticSmoothReduction

/-!
# Smooth reduction under extensions of valuation rings

A local map of valuation rings preserves primitive projective coordinates.
The induced residue field map is injective, so actual nonsingular reduction
is both preserved and reflected, without good-reduction assumptions.
-/

@[expose] public section

namespace FLT.Mazur

open IsLocalRing WeierstrassCurve WeierstrassCurve.Projective

variable {K L : Type*} [Field K] [Field L]
  (A : ValuationSubring K) (B : ValuationSubring L) (W : WeierstrassCurve A)
  (f : K →+* L) (g : A →+* B)
  (hc : (algebraMap B L).comp g = f.comp (algebraMap A K))

/-- Compatible integral and field maps induce an actual projective point homomorphism. -/
noncomputable def integralProjectiveExtension :
    (W.map (algebraMap A K)).toProjective.Point →+
      ((W.map g).map (algebraMap B L)).toProjective.Point :=
  extensionProjectiveHom _ f _ (by rw [map_map, map_map, hc])

/-- A primitive representative extends to a primitive representative of the extended point. -/
def PrimitiveLift.extension {P : (W.map (algebraMap A K)).toProjective.Point}
    (v : PrimitiveLift A P.point) :
    PrimitiveLift B (integralProjectiveExtension A B W f g hc P).point where
  coords := g ∘ v.coords
  primitive := by
    obtain ⟨i, hi⟩ := v.primitive
    exact ⟨i, hi.map g⟩
  represents := by
    change (⟦fun i => ((g (v.coords i) : B) : L)⟧ : PointClass L) =
      extensionPointClass f P.point
    conv_rhs => rw [← v.represents]
    apply congrArg Quotient.mk''
    funext i
    exact RingHom.congr_fun hc (v.coords i)

variable [IsLocalHom g]

/-- The actual extended point has smooth reduction exactly when the original point does. -/
theorem smoothReduction_integralProjectiveExtension
    (P : (W.map (algebraMap A K)).toProjective.Point) :
    SmoothReduction B (W.map g) (integralProjectiveExtension A B W f g hc P) ↔
      SmoothReduction A W P := by
  let v := primitiveLift A W P
  let w := v.extension A B W f g hc
  unfold SmoothReduction
  rw [projectiveReduction_eq B (W.map g) _ w, projectiveReduction_eq A W P v]
  change ((W.map g).map (residue B)).toProjective.Nonsingular
    (residue B ∘ g ∘ v.coords) ↔
    (W.map (residue A)).toProjective.Nonsingular (residue A ∘ v.coords)
  have hm : (W.map (residue A)).map (ResidueField.map g) =
      (W.map g).map (residue B) := by
    rw [map_map, map_map, ResidueField.map_comp_residue]
  have hv : residue B ∘ g ∘ v.coords = ResidueField.map g ∘ (residue A ∘ v.coords) := by
    funext i
    exact (ResidueField.map_residue g (v.coords i)).symm
  rw [hv, ← hm]
  exact (W.map (residue A)).toProjective.map_nonsingular (ResidueField.map g).injective _

end FLT.Mazur
