/-
Copyright (c) 2026 The FLT Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The FLT Project
-/
module

public import FLT.Mazur.CartierCharts
public import Mathlib.RingTheory.PicardGroup

/-!
# The module of a divisor on a Cartier chart

On a chart with regular equation `a`, the ideal `(a)` is a free module of rank one.
Its dual is the chart module for O(D). Multiplication identifies the tensor product
of two such ideals with their product; dualizing gives the sum formula for chart modules.
These constructions use actual ideals and their duals, and work over rings with zero divisors.

This is the affine chart part of FC10. Gluing these modules into a sheaf and proving
compatibility with sheaf restriction remain separate tasks. In particular, no module
of global sections is asserted to be free on an arbitrary affine open.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct

universe u

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace FLT.Mazur.FCurve

namespace CartierModule

variable {R : Type u} [CommRing R]

/-- Multiplication by a specified generator, with values in the actual ideal. -/
def generatorMap (I : Ideal R) (a : R) (h : I = Ideal.span {a}) : R →ₗ[R] I :=
  (LinearMap.mulRight R a).codRestrict I fun r ↦ by
    rw [h, Ideal.mem_span_singleton]
    exact ⟨r, mul_comm _ _⟩

@[simp]
lemma generatorMap_coe (I : Ideal R) (a : R) (h : I = Ideal.span {a}) (r : R) :
    (generatorMap I a h r : R) = r * a := rfl

/-- A regular equation trivializes its ideal, including over nonreduced rings. -/
def idealEquiv (I : Ideal R) (a : R) (ha : IsRegular a)
    (h : I = Ideal.span {a}) : R ≃ₗ[R] I :=
  LinearEquiv.ofBijective (generatorMap I a h) ⟨fun _ _ he ↦ ha.2 (congrArg Subtype.val he),
    fun x ↦ by
      have hx := x.property
      have hx : (x : R) ∈ Ideal.span {a} := h ▸ hx
      rw [Ideal.mem_span_singleton] at hx
      obtain ⟨r, hr⟩ := hx
      exact ⟨r, Subtype.ext (by simpa [mul_comm] using hr.symm)⟩⟩

@[simp]
lemma idealEquiv_coe (I : Ideal R) (a : R) (ha : IsRegular a)
    (h : I = Ideal.span {a}) (r : R) : (idealEquiv I a ha h r : R) = r * a := rfl

/-- The chart module is the dual of the divisor's ideal. -/
abbrev Dual (I : Ideal R) := Module.Dual R I

/-- Evaluation at the chosen generator trivializes the dual ideal. -/
def dualEquiv (I : Ideal R) (a : R) (ha : IsRegular a)
    (h : I = Ideal.span {a}) : Dual I ≃ₗ[R] R :=
  (idealEquiv I a ha h).dualMap ≪≫ₗ LinearMap.ringLmapEquivSelf R R R

@[simp]
lemma dualEquiv_apply (I : Ideal R) (a : R) (ha : IsRegular a)
    (h : I = Ideal.span {a}) (f : Dual I) :
    dualEquiv I a ha h f = f (idealEquiv I a ha h 1) := rfl

/-- Invertibility is Mathlib's canonical contraction condition. -/
lemma ideal_invertible (I : Ideal R) (a : R) (ha : IsRegular a)
    (h : I = Ideal.span {a}) : Module.Invertible R I :=
  Module.Invertible.congr (idealEquiv I a ha h)

lemma dual_invertible (I : Ideal R) (a : R) (ha : IsRegular a)
    (h : I = Ideal.span {a}) : Module.Invertible R (Dual I) :=
  Module.Invertible.congr (dualEquiv I a ha h).symm

/-- A functional on a principal ideal is determined by its value on the generator. -/
lemma dual_ext (I : Ideal R) (a : R) (ha : IsRegular a) (h : I = Ideal.span {a})
    {f g : Dual I} (he : f (idealEquiv I a ha h 1) = g (idealEquiv I a ha h 1)) :
    f = g :=
  (dualEquiv I a ha h).injective he

/-- Tensoring the two trivializations gives the multiplication isomorphism of ideals. -/
def idealTensorEquiv (I J : Ideal R) (a b : R) (ha : IsRegular a) (hb : IsRegular b)
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {b}) : I ⊗[R] J ≃ₗ[R] ↥(I * J) :=
  TensorProduct.congr (idealEquiv I a ha hI).symm (idealEquiv J b hb hJ).symm ≪≫ₗ
    TensorProduct.lid R R ≪≫ₗ
      idealEquiv (I * J) (a * b) (ha.mul hb)
        (by rw [hI, hJ, Ideal.span_singleton_mul_span_singleton])

/-- The isomorphism is actual multiplication, rather than an arbitrary rank-one comparison. -/
@[simp]
lemma idealTensorEquiv_tmul (I J : Ideal R) (a b : R) (ha : IsRegular a) (hb : IsRegular b)
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {b}) (x : I) (y : J) :
    (idealTensorEquiv I J a b ha hb hI hJ (x ⊗ₜ[R] y) : R) = (x : R) * (y : R) := by
  obtain ⟨r, rfl⟩ := (idealEquiv I a ha hI).surjective x
  obtain ⟨s, rfl⟩ := (idealEquiv J b hb hJ).surjective y
  simp [idealTensorEquiv, mul_left_comm, mul_comm]

/-- The multiplication equivalence does not depend on the regular generators. -/
lemma idealTensorEquiv_eq (I J : Ideal R) (a b c d : R)
    (ha : IsRegular a) (hb : IsRegular b) (hc : IsRegular c) (hd : IsRegular d)
    (hIa : I = Ideal.span {a}) (hJb : J = Ideal.span {b})
    (hIc : I = Ideal.span {c}) (hJd : J = Ideal.span {d}) :
    idealTensorEquiv I J a b ha hb hIa hJb = idealTensorEquiv I J c d hc hd hIc hJd := by
  apply LinearEquiv.toLinearMap_injective
  ext x y
  simp

/-- The chart form of O(D + E) = O(D) tensor O(E), in the reverse direction. -/
def dualTensorEquiv (I J : Ideal R) (a b : R) (ha : IsRegular a) (hb : IsRegular b)
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {b}) :
    Dual I ⊗[R] Dual J ≃ₗ[R] Dual (I * J) := by
  letI := ideal_invertible I a ha hI
  letI := ideal_invertible J b hb hJ
  exact TensorProduct.dualDistribEquiv R I J ≪≫ₗ
    (idealTensorEquiv I J a b ha hb hI hJ).symm.dualMap

/-- Pure tensors of functionals evaluate on products by multiplying their values. -/
@[simp]
lemma dualTensorEquiv_apply (I J : Ideal R) (a b : R) (ha : IsRegular a) (hb : IsRegular b)
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {b})
    (f : Dual I) (g : Dual J) (x : I) (y : J) :
    dualTensorEquiv I J a b ha hb hI hJ (f ⊗ₜ[R] g)
      (idealTensorEquiv I J a b ha hb hI hJ (x ⊗ₜ[R] y)) = f x * g y := by
  simp [dualTensorEquiv, LinearEquiv.dualMap, mul_comm]

/-- The sum comparison is independent of the equations used to construct it. -/
lemma dualTensorEquiv_eq (I J : Ideal R) (a b c d : R)
    (ha : IsRegular a) (hb : IsRegular b) (hc : IsRegular c) (hd : IsRegular d)
    (hIa : I = Ideal.span {a}) (hJb : J = Ideal.span {b})
    (hIc : I = Ideal.span {c}) (hJd : J = Ideal.span {d}) :
    dualTensorEquiv I J a b ha hb hIa hJb = dualTensorEquiv I J c d hc hd hIc hJd := by
  unfold dualTensorEquiv
  congr 2
  exact congrArg LinearEquiv.symm
    (idealTensorEquiv_eq I J a b c d ha hb hc hd hIa hJb hIc hJd)

section Restriction

variable {S : Type u} [CommRing S]

/-- Restrict a functional when a regular equation stays regular under a ring map.
This is semilinear for the restriction map of rings, as required on affine opens. -/
def dualRestrict (σ : R →+* S) (I : Ideal R) (J : Ideal S) (a : R)
    (ha : IsRegular a) (hσa : IsRegular (σ a))
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {σ a}) : Dual I →ₛₗ[σ] Dual J where
  toFun f := (dualEquiv J (σ a) hσa hJ).symm (σ (dualEquiv I a ha hI f))
  map_add' f g := by simp
  map_smul' r f := by
    simp only [map_smulₛₗ, RingHom.id_apply, smul_eq_mul, map_mul]
    simpa only [smul_eq_mul] using
      (map_smul (dualEquiv J (σ a) hσa hJ).symm (σ r) (σ (dualEquiv I a ha hI f)))

/-- Restriction on the negative divisor module is the underlying ring map. -/
def idealRestrict (σ : R →+* S) (I : Ideal R) (J : Ideal S)
    (hIJ : I.map σ ≤ J) : I →ₛₗ[σ] J where
  toFun x := ⟨σ (x : R), hIJ (Ideal.mem_map_of_mem σ x.property)⟩
  map_add' x y := Subtype.ext (map_add σ (x : R) (y : R))
  map_smul' r x := Subtype.ext (map_mul σ r (x : R))

/-- Evaluation commutes with restriction on a Cartier chart. -/
lemma dualRestrict_apply (σ : R →+* S) (I : Ideal R) (J : Ideal S) (a : R)
    (ha : IsRegular a) (hσa : IsRegular (σ a))
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {σ a})
    (hIJ : I.map σ ≤ J) (f : Dual I) (x : I) :
    dualRestrict σ I J a ha hσa hI hJ f (idealRestrict σ I J hIJ x) = σ (f x) := by
  obtain ⟨r, rfl⟩ := (idealEquiv I a ha hI).surjective x
  have he : idealRestrict σ I J hIJ (idealEquiv I a ha hI r) =
      idealEquiv J (σ a) hσa hJ (σ r) := by
    apply Subtype.ext
    exact map_mul σ r a
  rw [he]
  have eval (K : Type u) [CommRing K] (L : Ideal K) (b : K) (hb : IsRegular b)
      (hL : L = Ideal.span {b}) (g : Dual L) (t : K) :
      g (idealEquiv L b hb hL t) = t * dualEquiv L b hb hL g := by
    have ht : idealEquiv L b hb hL t = t • idealEquiv L b hb hL 1 := by
      simpa using (map_smul (idealEquiv L b hb hL) t (1 : K))
    rw [ht, map_smul]
    rfl
  rw [eval, eval]
  simp [dualRestrict]

/-- The restriction map is uniquely characterized by its evaluation equation. -/
lemma dualRestrict_unique (σ : R →+* S) (I : Ideal R) (J : Ideal S) (a : R)
    (ha : IsRegular a) (hσa : IsRegular (σ a))
    (hI : I = Ideal.span {a}) (hJ : J = Ideal.span {σ a}) (hIJ : I.map σ ≤ J)
    (F : Dual I →ₛₗ[σ] Dual J)
    (hF : ∀ f x, F f (idealRestrict σ I J hIJ x) = σ (f x)) :
    F = dualRestrict σ I J a ha hσa hI hJ := by
  apply LinearMap.ext
  intro f
  apply dual_ext J (σ a) hσa hJ
  have he : idealRestrict σ I J hIJ (idealEquiv I a ha hI 1) =
      idealEquiv J (σ a) hσa hJ 1 := by
    apply Subtype.ext
    simp [idealRestrict]
  rw [← he, hF, dualRestrict_apply]

/-- Changing the local equation leaves restriction unchanged. -/
lemma dualRestrict_eq (σ : R →+* S) (I : Ideal R) (J : Ideal S) (a b : R)
    (ha : IsRegular a) (hb : IsRegular b)
    (hσa : IsRegular (σ a)) (hσb : IsRegular (σ b))
    (hIa : I = Ideal.span {a}) (hIb : I = Ideal.span {b})
    (hJa : J = Ideal.span {σ a}) (hJb : J = Ideal.span {σ b})
    (hIJ : I.map σ ≤ J) :
    dualRestrict σ I J a ha hσa hIa hJa = dualRestrict σ I J b hb hσb hIb hJb := by
  apply dualRestrict_unique σ I J b hb hσb hIb hJb hIJ
  exact fun f x ↦ dualRestrict_apply σ I J a ha hσa hIa hJa hIJ f x

end Restriction

end CartierModule

variable {X : Scheme.{u}}

/-- The dual of the ideal on an affine open. Freeness requires a Cartier chart. -/
abbrev divisorChartModule (I : X.IdealSheafData) (U : X.affineOpens) :=
  CartierModule.Dual (I.ideal U)

/-- A chosen local equation identifies the ideal with the structure ring. -/
def CartierChart.idealEquiv {I : X.IdealSheafData} {U : X.affineOpens}
    (h : CartierChart I U) : Γ(X, U) ≃ₗ[Γ(X, U)] I.ideal U :=
  CartierModule.idealEquiv _ h.choose h.choose_spec.1 h.choose_spec.2

/-- The corresponding trivialization of the positive divisor module. -/
def CartierChart.dualEquiv {I : X.IdealSheafData} {U : X.affineOpens}
    (h : CartierChart I U) : divisorChartModule I U ≃ₗ[Γ(X, U)] Γ(X, U) :=
  CartierModule.dualEquiv _ h.choose h.choose_spec.1 h.choose_spec.2

lemma CartierChart.ideal_invertible {I : X.IdealSheafData} {U : X.affineOpens}
    (h : CartierChart I U) : Module.Invertible Γ(X, U) (I.ideal U) :=
  Module.Invertible.congr h.idealEquiv

lemma CartierChart.dual_invertible {I : X.IdealSheafData} {U : X.affineOpens}
    (h : CartierChart I U) : Module.Invertible Γ(X, U) (divisorChartModule I U) :=
  Module.Invertible.congr h.dualEquiv.symm

/-- On a common Cartier chart, divisor addition gives the tensor product of dual ideals. -/
def CartierChart.sumEquiv {I J : X.IdealSheafData} {U : X.affineOpens}
    (hI : CartierChart I U) (hJ : CartierChart J U) :
    divisorChartModule I U ⊗[Γ(X, U)] divisorChartModule J U ≃ₗ[Γ(X, U)]
      divisorChartModule (I * J) U :=
  CartierModule.dualTensorEquiv _ _ hI.choose hJ.choose hI.choose_spec.1 hJ.choose_spec.1
    hI.choose_spec.2 hJ.choose_spec.2

/-- The restriction of a regular equation to an affine subopen is regular. -/
lemma regular_restrict {U V : X.affineOpens} (hUV : U ≤ V)
    {a : Γ(X, V)} (ha : IsRegular a) :
    IsRegular ((X.presheaf.map (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom a) := by
  let σ := (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom
  have hσ : σ.Flat := by
    simpa [Scheme.Hom.appLE] using Scheme.Hom.flat_appLE (𝟙 X) V.2 U.2 hUV
  let := σ.toAlgebra
  let : Module.Flat Γ(X, V) Γ(X, U) := hσ
  rw [← isLeftRegular_iff_isRegular]
  simpa only [IsSMulRegular, IsLeftRegular, Algebra.smul_def, RingHom.algebraMap_toAlgebra]
    using (Module.Flat.isSMulRegular_of_isRegular (M := Γ(X, U)) ha)

/-- An equation for an ideal restricts to its image under the section map. -/
lemma ideal_eq_span_restrict (I : X.IdealSheafData) {U V : X.affineOpens}
    (hUV : U ≤ V) {a : Γ(X, V)} (ha : I.ideal V = Ideal.span {a}) :
    I.ideal U = Ideal.span
      {(X.presheaf.map (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom a} := by
  rw [← I.map_ideal hUV, ha, Ideal.map_span, Set.image_singleton]
  rfl

/-- Restriction between dual modules on nested Cartier charts. -/
def CartierChart.dualRestrict {I : X.IdealSheafData} {U V : X.affineOpens}
    (hV : CartierChart I V) (hUV : U ≤ V) :
    divisorChartModule I V →ₛₗ[(X.presheaf.map
      (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom] divisorChartModule I U :=
  CartierModule.dualRestrict
    (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom
    (I.ideal V) (I.ideal U) hV.choose hV.choose_spec.1
    (regular_restrict hUV hV.choose_spec.1) hV.choose_spec.2
    (ideal_eq_span_restrict I hUV hV.choose_spec.2)

/-- Restriction of a dual section evaluates as the restriction of its evaluation. -/
lemma CartierChart.dualRestrict_apply {I : X.IdealSheafData} {U V : X.affineOpens}
    (hV : CartierChart I V) (hUV : U ≤ V)
    (f : divisorChartModule I V) (x : I.ideal V) :
    hV.dualRestrict hUV f
      (CartierModule.idealRestrict _ _ _ (I.map_ideal hUV).le x) =
        (X.presheaf.map (homOfLE (show U.1 ≤ V.1 from hUV)).op).hom (f x) :=
  CartierModule.dualRestrict_apply _ _ _ _ _ _ _ _ _ f x

/-- Every point has an affine neighborhood with an invertible dual ideal module. -/
theorem EffectiveCartier.exists_invertible_dual {I : X.IdealSheafData}
    (hI : EffectiveCartier I) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Module.Invertible Γ(X, U) (divisorChartModule I U) := by
  obtain ⟨U, hxU, hU⟩ := hI x
  exact ⟨U, hxU, CartierChart.dual_invertible hU⟩

/-- Two effective Cartier divisors have a common chart carrying the sum comparison. -/
theorem EffectiveCartier.exists_sumEquiv {I J : X.IdealSheafData}
    (hI : EffectiveCartier I) (hJ : EffectiveCartier J) (x : X) :
    ∃ U : X.affineOpens, x ∈ U.1 ∧
      Nonempty (divisorChartModule I U ⊗[Γ(X, U)] divisorChartModule J U ≃ₗ[Γ(X, U)]
        divisorChartModule (I * J) U) := by
  obtain ⟨V, hxV, hV⟩ := hI x
  obtain ⟨U, hxU, hUV, hU⟩ := hJ.exists_chart_le hxV
  exact ⟨U, hxU, ⟨(CartierChart.mono hV hUV).sumEquiv hU⟩⟩

/-- The empty divisor has the trivial dual module on every affine open. -/
def emptyDivisorChartEquiv (U : X.affineOpens) :
    divisorChartModule (⊤ : X.IdealSheafData) U ≃ₗ[Γ(X, U)] Γ(X, U) :=
  (cartierChart_top U).dualEquiv

end FLT.Mazur.FCurve
