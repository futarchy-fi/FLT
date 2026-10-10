/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassDividedInitialBoundaryGeometry
public import FLT.Mazur.WeierstrassDividedInitialLineIntersection
public import FLT.Mazur.WeierstrassDividedOlderGlobalComponentSections

/-!
# Exact initial-parameter intersections with the first retained lines

Both original signed punctures are full scheme pullbacks. The proof first
uses the complete tensor-chart intersection, then restricts along each
monomorphic full conic parameter, so no additional intersections are assumed.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
namespace FLT.Mazur.WeierstrassDividedDepth
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
universe u
variable {R : Type u} [CommRing R] [IsDomain R] [IsBezout R] [IsLocalRing R]
  {W : WeierstrassCurve R} {π : R} (hπ : π ≠ 0) {start n depth : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (D : SplitNodeDepth W π depth) (h1 : 1 ≤ n)
  (hstart : 0 < start) (hk : 2 * (start + 1) ≤ depth)
  (r : ℕ) (hr : 1 + r ≤ n)
open WeierstrassModificationX WeierstrassSuccessiveX
local notation "K" => ResidueField R
local notation "d" => data (Fin.mk 0 (Nat.zero_lt_succ n))
local notation "a" => residue R W.a₁
local notation "c" => residue R (Data.b6 d)
local notation "hc" => Iff.mpr (residue_eq_zero_iff _)
  (WeierstrassDilatation.divided_constant_mem D start (by omega)
    (Data.b6 d) (Data.factor6 d))
local notation "ha" => residue_tangent_isUnit D
local notation "tangent" => WeierstrassDilatation.residueTangentUnit D
local notation "p" => Spec.map (CommRingCat.ofHom (AlgHom.toRingHom (conicZeroPuncture c hc)))
local notation "ρ₁" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (tangent)⁻¹)))
local notation "ρ₂" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (PolygonScaledReciprocal.reciprocal (-tangent)⁻¹)))
local notation "P₁" => initialGlobalConicFirstParameter hπ data D (1 + r) hr hstart (by omega)
local notation "P₂" => initialGlobalConicSecondParameter hπ data D (1 + r) hr hstart (by omega)
local notation "G₁" => olderGlobalMiddleFirstLine hπ data D 0 h1 r hr hstart hk
local notation "G₂" => olderGlobalMiddleSecondLine hπ data D 0 h1 r hr hstart hk

local notation "E" => residueFiberIso D start hstart (by omega)
  (Data.b3 d) (Data.b4 d) (Data.b6 d) (Data.factor3 d) (Data.factor4 d)
local notation "C₁" => Iso.inv (conicFirstParameterIso a c ha) ≫
  conicFirstOpenImmersion a c ≫ fiberConicImmersion a c ≫ Iso.hom E
local notation "C₂" => Iso.inv (conicSecondParameterIso a c ha) ≫
  conicSecondOpenImmersion a c ≫ fiberConicImmersion a c ≫ Iso.hom E
local notation "g" => globalInitialTensorChart hπ data K (1 + r) hr

/-- The complete first initial parameter meets its retained line in exactly one puncture. -/
theorem initialGlobalFirstParameter_isPullback :
    IsPullback (ρ₁ ≫ ProjectiveLine.overlapLeft K) p G₁ P₁ := by
  have H := initialRetainedLine_isPullback hπ data D h1 hstart hk
    0 (by simp) (tangent)⁻¹ r hr
  have B := initialConicFirstLine_boundary_spec hπ data D h1 hstart hk
  rw [conicPuncturedFirst_spec c hc (W.map (residue R)) ha] at B
  simp only [Category.assoc] at B
  rw [← B] at H
  have H' : IsPullback (ρ₁ ≫ ProjectiveLine.overlapLeft K) (p ≫ C₁) G₁ g := H
  have T : IsPullback (𝟙 _) p (p ≫ C₁) C₁ :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp, Category.assoc, initialGlobalConicFirstParameter,
    initialGlobalConic, initialGlobalResidueFiberChart] using T.paste_horiz H'

/-- The opposite complete parameter retains precisely the negative reciprocal puncture. -/
theorem initialGlobalSecondParameter_isPullback :
    IsPullback (ρ₂ ≫ ProjectiveLine.overlapLeft K) p G₂ P₂ := by
  have H := initialRetainedLine_isPullback hπ data D h1 hstart hk
    (-a) (by simp) (-tangent)⁻¹ r hr
  have B := initialConicSecondLine_boundary_spec hπ data D h1 hstart hk
  rw [conicPuncturedSecond_spec c hc (W.map (residue R)) ha] at B
  simp only [Category.assoc] at B
  rw [← B] at H
  have H' : IsPullback (ρ₂ ≫ ProjectiveLine.overlapLeft K) (p ≫ C₂) G₂ g := H
  have T : IsPullback (𝟙 _) p (p ≫ C₂) C₂ :=
    IsPullback.of_horiz_isIso_mono ⟨by simp only [Category.id_comp]⟩
  simpa only [Category.id_comp, Category.assoc, initialGlobalConicSecondParameter,
    initialGlobalConic, initialGlobalResidueFiberChart] using T.paste_horiz H'

/-- The first actual intersection is the original Laurent parameter scheme. -/
def initialGlobalFirstParameterPullbackIso :=
  (initialGlobalFirstParameter_isPullback hπ data D h1 hstart hk r hr).isoPullback

/-- The opposite actual intersection is also the original Laurent parameter scheme. -/
def initialGlobalSecondParameterPullbackIso :=
  (initialGlobalSecondParameter_isPullback hπ data D h1 hstart hk r hr).isoPullback

/-- The first intersection retains the original positive reciprocal line projection. -/
@[reassoc] theorem initialGlobalFirstParameterPullbackIso_line :
    (initialGlobalFirstParameterPullbackIso hπ data D h1 hstart hk r hr).hom ≫
      pullback.fst G₁ P₁ = ρ₁ ≫ ProjectiveLine.overlapLeft K :=
  (initialGlobalFirstParameter_isPullback hπ data D h1 hstart hk r hr).isoPullback_hom_fst

/-- The first intersection retains the original full parameter puncture. -/
@[reassoc] theorem initialGlobalFirstParameterPullbackIso_parameter :
    (initialGlobalFirstParameterPullbackIso hπ data D h1 hstart hk r hr).hom ≫
      pullback.snd G₁ P₁ = p :=
  (initialGlobalFirstParameter_isPullback hπ data D h1 hstart hk r hr).isoPullback_hom_snd

/-- The second intersection retains the negative reciprocal line projection. -/
@[reassoc] theorem initialGlobalSecondParameterPullbackIso_line :
    (initialGlobalSecondParameterPullbackIso hπ data D h1 hstart hk r hr).hom ≫
      pullback.fst G₂ P₂ = ρ₂ ≫ ProjectiveLine.overlapLeft K :=
  (initialGlobalSecondParameter_isPullback hπ data D h1 hstart hk r hr).isoPullback_hom_fst

/-- The second intersection retains the opposite full parameter puncture. -/
@[reassoc] theorem initialGlobalSecondParameterPullbackIso_parameter :
    (initialGlobalSecondParameterPullbackIso hπ data D h1 hstart hk r hr).hom ≫
      pullback.snd G₂ P₂ = p :=
  (initialGlobalSecondParameter_isPullback hπ data D h1 hstart hk r hr).isoPullback_hom_snd

end FLT.Mazur.WeierstrassDividedDepth
