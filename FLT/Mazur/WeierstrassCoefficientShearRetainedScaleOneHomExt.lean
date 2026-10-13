/-
Copyright (c) 2026 krandder. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: krandder
-/
module

public import FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneDescent
import all FLT.Mazur.WeierstrassCoefficientShearRetainedScaleOneDescent

/-!
# Full retained scale-one hom-ext and coefficient structure

The original conic and incidence line determine maps on the entire equation,
and descent preserves the coefficient structure when its inputs do.
-/

@[expose] public noncomputable section
open AlgebraicGeometry CategoryTheory Polynomial
namespace FLT.Mazur.WeierstrassDividedDepth
open WeierstrassSuccessiveX WeierstrassModificationX
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option quotPrecheck false
universe u
variable {R : Type u} [CommRing R]
  {W : WeierstrassCurve R} {π : R} {start n : ℕ}
  (data : (i : Fin (n + 1)) → Data W π (start + i.val))
  (S : Type u) [Field S] [Algebra R S] (r : S)
  (t : ℕ) (ht : t ≤ n) (i : Fin t)
local notation "d" => data (Fin.mk (i.val + 1) (by omega))
local notation "s₀" => π ^ (start + i.val)
local notation "a" => (rootShearCurve (W.map (algebraMap R S)) r).a₁
local notation "c" => algebraMap R S (Data.b6 d)
local notation "T" => ScalarExtension W s₀ π (Data.b3 d) (Data.b4 d) (Data.b6 d) S

local notation "E" => coefficientShearRetainedScaleOneTensorIso data S r t ht i

variable (hs : algebraMap R S (π ^ (start + i.val)) = 1) (hp : algebraMap R S π = 0)
  (h3 : algebraMap R S (Data.b3 (data ⟨i.val + 1, by omega⟩)) = 0)
  (h4 : algebraMap R S (Data.b4 (data ⟨i.val + 1, by omega⟩)) = 0)
  (hr : r ^ 2 + algebraMap R S W.a₁ * r - algebraMap R S W.a₂ = 0)
local notation "C" => tensorShearScaleOneConicImmersion W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr
local notation "L" => Spec.map (CommRingCat.ofHom (tensorShearScaleOneIncidenceMap W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr).toRingHom)
variable (ha : IsUnit (rootShearCurve (W.map (algebraMap R S)) r).a₁)
local notation "H" => tensorShearScaleOneFiberIso W s₀ π
  (Data.b3 d) (Data.b4 d) (Data.b6 d) S r hs hp h3 h4 hr

include ha in
/-- Both entire original components jointly determine maps out of the retained equation. -/
theorem coefficientShearRetainedScaleOne_hom_ext {Y : Scheme.{u}}
    (m₁ m₂ : coefficientShearAtlasObject data S r t ht (.inr i) ⟶ Y)
    (hf : C ≫ (E).inv ≫ m₁ = C ≫ (E).inv ≫ m₂)
    (hg : L ≫ (E).inv ≫ m₁ = L ≫ (E).inv ≫ m₂) : m₁ = m₂ := by
  apply (cancel_epi (E).inv).mp
  apply (cancel_epi (H).hom).mp
  apply fullFiber_components_hom_ext a c ha
  · simpa only [tensorShearScaleOneFiberIso_incidence_assoc] using hg
  · simpa only [tensorShearScaleOneFiberIso_conic_assoc] using hf

variable {Y : Scheme.{u}} (f : Spec (.of (ConicCoordinate
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (Data.b6 (data ⟨i.val + 1, by omega⟩))))) ⟶ Y)
  (g : ProjectiveLine.chart S ⟶ Y)
  (w₁ : Spec.map (CommRingCat.ofHom (conicFirstIncidencePoint
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (Data.b6 (data ⟨i.val + 1, by omega⟩))) ha).toRingHom) ≫ f =
      ProjectiveLine.chartZero S ≫ g)
  (w₂ : Spec.map (CommRingCat.ofHom (conicSecondIncidencePoint
    (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (Data.b6 (data ⟨i.val + 1, by omega⟩))) ha).toRingHom) ≫ f =
      Spec.map (CommRingCat.ofHom (aeval
        (-(rootShearCurve (W.map (algebraMap R S)) r).a₁)).toRingHom) ≫ g)
local notation "D" => coefficientShearRetainedScaleOneDesc
  data S r t ht i hs hp h3 h4 hr ha f g w₁ w₂
variable (p : Y ⟶ Spec (.of S))
  (hf : f ≫ p = conicStructure (rootShearCurve (W.map (algebraMap R S)) r).a₁
    (algebraMap R S (data ⟨i.val + 1, by omega⟩).b6))
  (hg : g ≫ p = ProjectiveLine.chartToBase S)

include hf hg in
/-- Full scale-one descent retains the coefficient structure of both original component maps. -/
theorem coefficientShearRetainedScaleOneDesc_structure :
    D ≫ p = coefficientShearAtlasStructure data S r t ht (.inr i) := by
  have hbase : (E).inv ≫ coefficientShearAtlasStructure data S r t ht (.inr i) =
      Spec.map (CommRingCat.ofHom (algebraMap S T)) := by
    change (successiveCoefficientShearIso _ _ _ _ _ _ _ _).inv ≫
      Spec.map (CommRingCat.ofHom (algebraMap S _)) = _
    rw [← successiveCoefficientShearIso_structure, Iso.inv_hom_id_assoc]
  apply coefficientShearRetainedScaleOne_hom_ext data S r t ht i hs hp h3 h4 hr ha
  · rw [hbase, coefficientShearRetainedScaleOneDesc_conic_assoc, hf,
      tensorShearScaleOneConicImmersion_eq_spec]
    exact (terminalComponent_algebra_structure _).symm
  · rw [hbase, coefficientShearRetainedScaleOneDesc_incidence_assoc, hg]
    exact (terminalComponent_algebra_structure _).symm

/-- The descended scale-one chart map is an actual morphism over the coefficient field. -/
def coefficientShearRetainedScaleOneOverDesc :
    Over.mk (coefficientShearAtlasStructure data S r t ht (.inr i)) ⟶ Over.mk p :=
  Over.homMk D (coefficientShearRetainedScaleOneDesc_structure
    data S r t ht i hs hp h3 h4 hr ha f g w₁ w₂ p hf hg)

end FLT.Mazur.WeierstrassDividedDepth
