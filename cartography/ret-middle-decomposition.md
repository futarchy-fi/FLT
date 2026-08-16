# R=T arithmetic middle — S/M decomposition of A2, A6, A7 (P1 decomposition execution)

Target: the three XL nodes of `cartography/r-eq-t-reconciled.md` §2.2 that the R=T
panel ruled decomposable (`panel/ret-adjudication.md` ruling 3, `panel/ret-dependency.md`
§2): **A2** (Galois rep into the Hecke algebra, split per adjudication into pseudo-rep
construction / G17 lifting / T_𝔪-valued globalization), **A6** (local flat deformation
condition at ℓ), **A7** (instantiation of the DONE abstract patching engine).
**The analytic block A9/A10 is EXCLUDED** per the same ruling ("the one true wall,
sequenced last by design") — nothing below touches base change, JL, or mult one.
Every node is S or M — one agent, one focused session (S ≈ one lemma/half-file,
M ≈ one tight file). Working-tree document only; not committed, not pushed.

Verification basis (2026-08-16): FLT repo greps are direct (`grep` of `/home/agent/FLT`,
local tip = `e99f167` era tree; **no vendored Mathlib** — `.lake/` absent — so Mathlib
claims are checked against live mathlib4 docs/web, flagged `(mathlib-web)` where
load-bearing, unlike the zeta decomposition which grepped a pinned copy).
Literature spot-checks (web): Nyssen, *Pseudo-représentations*, Math. Ann. 306 (1996)
257–283, and Rouquier, *Caractérisation des caractères et pseudo-caractères*,
J. Algebra 180 (1996) 571–586 — both **verified** to prove residually-absolutely-
irreducible pseudo-character lifting over local Henselian rings, independently, building
on Taylor (Duke 63, 1991); the dim-2 case actually needed is already in Wiles,
*On ordinary λ-adic representations* (Invent. Math. 94, **1988**) §2 — pre-1990, hence
`knownin1980s`-eligible under the repo's era discipline, unlike the general
Nyssen/Rouquier statement.

## Standing context (what exists, one paragraph)

The consumer end is fully real: `ker_RtoT_le_nilradical`
(`FLT/Patching/REqualsT.lean:86`) is proved, and its `variable` block (`:24-81`) is the
**exact instantiation contract** for A7 — every obligation below is named against it.
The Hecke algebra is real and sorry-free: `HeckeAlgebra D 𝒮`
(`FLT/AutomorphicForm/QuaternionAlgebra/HeckeOperators/Concrete.lean:881-885`,
commutative `:906-920`, Noetherian `:1067-1077`, faithful on forms `:1080`), with TW
level data `U₁Data` (`:374-385`: bad set `S`, TW set `Q`, order-`p` characters) and the
TW local level `GL2.localPTameLevel` already in the `U₁` definition. The deformation
side has the functor stack (`FLT/Deformations/LiftFunctor.lean`: `repnFunctor`,
`liftFunctor`, `detConditionFunctor`, `unramifiedFunctor`, trace/narrow-trace
functors — all with proved `map` fields **except** `flatFunctor.map` at `:117`) and the
two corepresentability keystones sorried (`FLT/Deformations/Representable.lean:38,106`
= A4, out of mandate but consumed). Coefficient choice fixed once here: ℓ ≥ 5
(`hl : 3 < l`, `Representable.lean:59`), so 2 is invertible and **Wiles–Taylor
(trace, det) pseudo-representations suffice; Chenevier determinants are NOT needed**
(Mathlib has the Roby `PolynomialLaw` groundwork, `Mathlib.RingTheory.PolynomialLaw.
Basic` (mathlib-web), but no determinant laws and no pseudo-representations of any
flavor — and `grep -ri pseudo FLT/` returns nothing representation-theoretic, so Part P
starts from a blank page by design, not oversight).

Notation: `F` totally real of even degree, ℓ ≥ 5 unramified in `F`, `𝓞` = coefficient
ring (complete Noetherian local ℤ_ℓ-algebra, finite residue field κ), `G_{F,Σ}` the
Galois group unramified outside Σ, `T = HeckeAlgebra D 𝒮`, `𝔪` a non-Eisenstein maximal
ideal, `ad⁰ρ̄` trace-zero adjoint, `q := dim_κ H¹_{L^⊥}(G_{F,Σ}, ad⁰ρ̄(1))`.

---

## Part P — A2(a): pseudo-representation of the Hecke algebra

**P1. Pseudo-representation, the definition.** Structure `PseudoRep G A` (2-dimensional,
Wiles-style): continuous `t : G → A`, continuous multiplicative `d : G →* Aˣ`, with
`t 1 = 2`, symmetry `t (gh) = t (hg)`, and the dim-2 identity
`t(g)t(h) = t(gh) + d(h)·t(gh⁻¹)`; base-change map along continuous ring homs.
*Size S.* Deps: none (Mathlib `ContinuousMonoidHom`; no prior art to port — verified
above). Sketch: pure structure + functoriality lemmas; requires `2` invertible nowhere
in the definition, only in Part L.

**P2. Trace of a representation is a pseudo-representation.** For
`ρ : G →ₜ* GL (Fin 2) A`: `(tr ρ, det ρ)` is a `PseudoRep`, invariant under conjugation
and compatible with base change; conversely `tr` determines char polys:
`charpoly (ρ g) = X² − t(g)X + d(g)`.
*Size S.* Deps: P1 (Mathlib `Matrix.trace`, Cayley–Hamilton `Matrix.aeval_self_charpoly`).
Sketch: the dim-2 identity *is* Cayley–Hamilton for 2×2 traced against `h`.

**P3. Rigidity and limits.** (i) Two continuous `PseudoRep`s into a Hausdorff
topological ring agreeing on a dense subset of `G` are equal; (ii) a compatible family
of `PseudoRep`s into an inverse limit `A = lim A_i` glues to a `PseudoRep` into `A`;
(iii) the values of a continuous `PseudoRep` on a topologically generating monoid lie in
any closed subring containing them on a dense subset.
*Size M.* Deps: P1 (Mathlib `Continuous.ext_on`, `IsClosed.mem_of_tendsto`; FLT
`Deformations/Algebra/InverseLimit`). Sketch: pointwise density arguments; (ii) is
componentwise.

**P4. Eigensystem decomposition of `T_𝔪[1/ℓ]`.** `T` is a finite 𝓞-module (from
`IsNoetherian R (HeckeAlgebra D 𝒮)` + `Module.Finite`, `Concrete.lean:1063-1071`);
hence `T_𝔪 ⊗_𝓞 Q̄_ℓ ≅ ∏ᵢ Eᵢ` (finite product of finite field extensions), minimal
primes ↔ eigensystems `λᵢ : T_𝔪 →ₐ Q̄_ℓ`, and `T_𝔪 ↪ ∏ᵢ 𝒪_{Eᵢ}` when `T_𝔪` is
𝓞-flat (reduce mod torsion; the reduced case suffices downstream).
*Size M.* Deps: G1 (Mathlib `IsArtinianRing` structure theorem /
`IsArtinianRing.equivPi` (mathlib-web); FLT
`Deformations/RepresentationTheory/IntegralClosure.lean` — the `IntegralClosure R A`
type synonym visibly built for this). Sketch: Artinian algebra over a field = product
of local Artinian; reducedness not assumed — kill nilpotents into the `𝒪ᵢ` statement.

**P5. The `T_𝔪`-valued pseudo-representation.** Given, for each eigensystem `λᵢ`, an
attached Galois rep `ρ_{λᵢ} : G_{F,S∪Q∪{ℓ}} → GL₂(𝒪_{Eᵢ})` with
`tr ρ_{λᵢ}(Frob_v) = λᵢ(T_v)`, `det ρ_{λᵢ}(Frob_v) = Nv` at good `v`
[**CONSUMED from G3/G15** — the Galois-reps chapter's attachment node, boundary per
`greps-adjudication.md`; interface shape = `IsAutomorphicOfLevel`,
`FLT/GaloisRepresentation/Automorphic.lean:67-94`]: the product pseudo-rep
`τ = (∏ tr ρ_{λᵢ}, ∏ det ρ_{λᵢ})` takes Frobenius values `(T_v, Nv) ∈ T_𝔪` on the
dense set of Frobenii, hence lands entirely in the closed subring `T_𝔪 ⊂ ∏ 𝒪ᵢ`, giving
continuous `τ : PseudoRep (G_{F,S∪Q∪{ℓ}}) T_𝔪` with `t(Frob_v) = T_v`.
*Size M.* Deps: P2, P3, P4, T3 [**Chebotarev tag**: density of Frobenii in `G_{F,Σ}` is
exactly the T3 wrapper]. Sketch: P3(iii) with dense subset = Frobenii; continuity of
`τ` from finiteness of the product.

## Part L — A2(b) = G17: pseudo-representation → genuine representation
*(This part IS the work breakdown of node G17 minted in `greps-adjudication.md` ruling 3.)*

**L1. Regular element.** If `ρ̄ : G → GL₂(κ)` is absolutely irreducible and
`char κ = ℓ ≥ 5`, there exists `g₀ ∈ G` with `ρ̄(g₀)` having distinct eigenvalues in κ̄
(`t̄(g₀)² ≠ 4·d̄(g₀)`), and after an unramified extension of κ we may take them in κ.
*Size S.* Deps: none (Mathlib `Matrix.IsDiagonalizable` fragments; finite group theory).
Sketch: if every element has equal eigenvalues, the image is (scalars)·(unipotents),
which is reducible over κ̄; ℓ > 2 makes "equal eigenvalues" ⟺ `t² = 4d`.

**L2. Lifting over a complete local ring** *(genuinely-hard flag)*. `A` complete
Noetherian local, finite residue field κ, `τ : PseudoRep G A` continuous with residual
pseudo-rep = `tr ρ̄`, `ρ̄` absolutely irreducible: there exists
`ρ : G → GL₂(A)` (abstract group hom at this node) with `(tr ρ, det ρ) = τ`.
*Size M.* Deps: P1, P2, L1. Sketch: Wiles 1988 §2 dim-2 argument — Hensel-lift the
eigenvalues of `τ`-data at `g₀` to idempotents, define matrix entries
`a(g), b(g)c(h)`-style as explicit polynomial expressions in `t`-values
(`t(g), t(gg₀), …`), verify multiplicativity from the P1 identities; irreducibility of
`ρ̄` supplies a nonvanishing `b̄(g₁)c̄(g₂)` to normalize. General reference
Nyssen 1996 / Rouquier 1996 (verified above); the dim-2 route avoids their Azumaya
machinery entirely.

**L3. Continuity of the lift.** The `ρ` of L2 is continuous, i.e. upgrades to
`G →ₜ* GL (Fin 2) A`, hence to an object of `(repnFunctor (Fin 2) G 𝓞).obj A` when `A`
is proartinian.
*Size S.* Deps: L2 (FLT `Deformations/LiftFunctor.lean:40` `repnFunctor`). Sketch: every
matrix entry of L2 is a fixed polynomial in finitely many continuous functions
`g ↦ t(g·c)`; `GL₂`-topology is the product topology on entries.

**L4. Carayol uniqueness.** Two continuous lifts of the same `τ` with residually
absolutely irreducible `ρ̄` are conjugate by an element of `ker(GL₂(A) → GL₂(κ))`;
in particular the L2/L3 construction is independent of choices up to the
`repnQuotFunctor` equivalence (`LiftFunctor.lean:79`).
*Size M.* Deps: L2, L3 (literature: Carayol, Contemp. Math. 165 (1994), Lemme 1
`(literature-verify)`; Mazur's Schur-lemma argument for deformations). Sketch:
successive-approximation over `A/𝔪ⁿ`: the difference of the two reps is a cocycle
valued in `ad`, trivialized level-by-level using `End_{κ[G]}(ρ̄) = κ` (abs irred).

## Part G — A2(c): T_𝔪-valued globalization (the node minted by ret-adjudication ruling 2)

**G1. Structure of `T_𝔪`.** Define the maximal-ideal localization/completion of the
finite 𝓞-algebra `T`: `T ⊗_𝓞 𝓞̂ ≅ ∏_{𝔪} T_𝔪`; each `T_𝔪` is a complete Noetherian
local 𝓞-algebra with finite residue field, and carries a `ProartinianCat 𝓞`-object
structure (`FLT/Deformations/Categories.lean`). [Mints the localization procedure
`ret-dependency.md` §1 found unclaimed — **A3-boundary node**.]
*Size M.* Deps: none (Mathlib `IsLocalization.AtPrime`, `IsAdicComplete`,
finite-algebra semilocal decomposition `(mathlib-web)`; `Concrete.lean` Noetherian
instances). Sketch: finite module over complete local ⇒ product of localizations at
maximals; completeness inherited.

**G2. The maximal ideal of a mod-ℓ eigensystem.** Given an automorphic `ρ̄` — i.e. a
witness `π : HeckeAlgebra D 𝒮 →ₐ[ℤ_[l]] A` as in `IsAutomorphicOfLevel`
(`Automorphic.lean:85`) with `A` residual — define `𝔪 := ker(T → κ)`, prove it maximal
with finite residue field; record the standing hypothesis "`𝔪` non-Eisenstein"
(= `ρ̄` absolutely irreducible) as the interface assumption. [Cross-ref: G3 non-vacuity
obligation, `greps-adjudication.md` ruling 4 — this node inherits, does not discharge,
the witness problem.]
*Size S.* Deps: G1. Sketch: kernel of map to a finite field from a finite algebra.

**G3. `ρ_𝔪 : G_{F,S∪Q∪{ℓ}} → GL₂(T_𝔪)`.** Apply L2/L3 to `A = T_𝔪` and `τ` from P5:
obtain a continuous rep with `charpoly (ρ_𝔪(Frob_v)) = X² − T_v·X + Nv` for all good
`v`, residually `≅ ρ̄`.
*Size S.* Deps: P5, L2, L3, G1, G2. Sketch: assembly; the char-poly identity is P2 + P5.

**G4. Determinant = cyclotomic.** `det ρ_𝔪 = ε_ℓ` as characters
`G_{F,S∪Q∪{ℓ}} → T_𝔪ˣ`, i.e. `ρ_𝔪 ∈ detConditionFunctor` (`LiftFunctor.lean:153`).
*Size S.* Deps: G3, T3 [**Chebotarev tag**]. Sketch: both continuous characters agree on
Frobenii (`Nv = ε_ℓ(Frob_v)`), which are dense (T3); Mathlib
`cyclotomicCharacter` already imported by `LiftFunctor.lean`.

**G5. `ρ_𝔪` satisfies the S-good local conditions** *(genuinely-hard flag)*.
(i) unramified outside `S ∪ Q ∪ {v|ℓ}`: `ρ_𝔪 ∈ unramifiedFunctor v` — inertia lands in
`ker` because it does in each `ρ_{λᵢ}` and `T_𝔪 ↪ ∏𝒪ᵢ` (P4) with L4 rigidity aligning
the conjugacies; (ii) trace 2 on (tame) inertia at `v ∈ S`
(`narrowTraceConditionFunctor`): same factor-wise argument on traces (traces need no
conjugation bookkeeping — this is why the pseudo-rep route is right); (iii) **flat at
`v | ℓ`**: `ρ_𝔪 ∈ flatFunctor v`, i.e. `IsFlatAt` (`GaloisRep.lean:395`) — each
`ρ_{λᵢ}` is flat (weight-2 Barsotti–Tate, part of the G-chapter attachment ledger; era
note: **post-1990 only** — Saito 2009/Breuil, per `greps-adjudication.md` ruling 1 Bp
reclass) and flatness of the glued `T_𝔪`-rep on artinian quotients follows via F2/F3
closure under products and subobjects.
*Size M (hard).* Deps: G3, P4, L4, F1, F2, F3, G-chapter Bp ledger. Sketch: per-condition,
factor-wise through `T_𝔪/𝔪ⁿ ↪ (∏𝒪ᵢ)/(lifted ideal)`-approximations; (iii) is the hard
third and the reason for the flag.

**G6. Classifying map and surjectivity `R^univ ↠ T_𝔪`.** Via corepresentability
[**consumes A4**: `narrowSLiftUniversalRingCorepresentableBy`,
`Representable.lean:113-116` — sorried today], G3–G5 give
`φ : narrowSLiftUniversalRing 𝓞 … ρ̄ → T_𝔪` in `ProartinianCat 𝓞`. Surjectivity: the
closed image contains all `tr ρ_𝔪(Frob_v) = T_v`; `T` is *by definition*
`Algebra.adjoin` of the `T_v` and `U_v` (`Concrete.lean:881-885`), and for `v ∈ Q` the
`U_v`-image is the tame-character eigenvalue of `ρ_𝔪|_{G_v}` (T8) — for the base-level
`Q = ∅` instantiation the `U_v` clause is vacuous [**D-9 tag**: the Q = ∅ hardcode's
"patching-side sufficiency proven by whoever pins" obligation is discharged only if T8
covers the `Q ≠ ∅` levels used in T11].
*Size M.* Deps: G3, G4, G5, T8, A4 [absent]. Sketch: universal property + topological
generation; Carayol's descent lemma (Contemp. Math. 165, Lemme 2) is *not* needed on
this route — the rep is already `T_𝔪`-valued.

## Part F — A6: the flat local condition at ℓ and its deformation ring
*(Easiest case by design: ℓ ≥ 5, ℓ unramified in `F`, weight 2 — squarely inside the
Fontaine–Laffaille range `[0, ℓ−2]`; FL theory is 1982 (Ann. Sci. ENS 15), pre-1990,
hence `knownin1980s`-eligible where axiomatization is chosen; the representability
statements are Ramakrishna, Compositio 87 (1993) — post-1990, era-note for the ledger.)*

**F1. `flatFunctor.map` (the `LiftFunctor.lean:117` sorry).** `IsFlatAt v` is preserved
by base change `R → S` in `ProartinianCat 𝓞`: a flat prolongation
(`HasFlatProlongationAt`, `GaloisRep.lean:387-397`) pushes forward along artinian
quotient maps. [Overlaps the A4 ready-now sorry set of the reconciled map §4 — claim
jointly, do not double-work.]
*Size M.* Deps: none (literature: Conrad, "Finite flat group schemes" in CSS
(Cornell–Silverman–Stevens), Thm 1.6 `(literature-verify)` — cited in-code). Sketch:
base-change the finite flat group scheme witness; the étale-generic-fibre condition is
stable under the coefficient extension.

**F2. Local flat lift functor.** Restrict along `toLocal v`: define the subfunctor of
`repnFunctor (Fin 2) (Γ F_v) 𝓞` of flat lifts of `ρ̄|_{G_v}` (mirror of `flatFunctor`
localized), and prove the global `flatFunctor` is its pullback.
*Size S.* Deps: F1 (FLT `GaloisRep.toLocal`, `Deformations/RepresentationTheory/
GaloisRep.lean`). Sketch: definitional transport; `IsFlatAt` is already a local-at-`v`
condition.

**F3. Closure properties of flat lifts.** On artinian coefficients, flat lifts are
closed under: subrepresentations, quotients, and finite products/fibre products (the
Ramakrishna conditions making "flat" a deformation condition).
*Size M.* Deps: F2 (literature: Ramakrishna 1993 §2; Raynaud, Bull. SMF 102 (1974) for
uniqueness of prolongations when `e = 1 < ℓ − 1`). Sketch: kernels/cokernels of maps of
finite flat group schemes over a DVR with `e < ℓ−1` are finite flat (Raynaud);
uniqueness gives functoriality of the prolongation, hence closure.

**F4. Corepresentability: `R^□,fl_v`.** The framed local flat lift functor is
corepresentable by a complete Noetherian local 𝓞-algebra `R^□,fl_v` (quotient of the
unrestricted framed local lifting ring).
*Size M.* Deps: F2, F3 [pattern-consumes A4's machinery,
`Representable.lean:36-38` — the framed/unconditional case]. Sketch: framed lifting
functors are corepresentable whenever `G_v` is topologically finitely generated
(true for local Galois groups — Jannsen/`(literature-verify)`); a closed condition
stable per F3 cuts out a quotient ring.

**F5. Formal smoothness of `R^□,fl_v`** *(genuinely-hard flag)*. In the FL range
(ℓ unramified, weight 2, ℓ ≥ 5), `R^□,fl_v` is formally smooth over 𝓞: every flat
deformation over `A/I` (small extension) lifts flatly to `A`.
*Size M (hard).* Deps: F3, F4 (literature: Fontaine–Laffaille 1982; Ramakrishna 1993
Thm 3.1; CHT (Pub. IHÉS 108) §2.4.1 for the `[F_v:ℚ_ℓ] > 1` unramified case
`(literature-verify)`). Sketch: transport to FL modules (weights {0,1}); the FL category
has vanishing obstruction (`Ext²= 0` / surjectivity on small extensions is a
filtered-module computation); back-transport along the FL equivalence.

**F6. Dimension / local Selmer count at ℓ.** Relative dimension of `R^□,fl_v` (with
det = ε_ℓ fixed) is `3 + [F_v : ℚ_ℓ]`; equivalently, with
`L_v := H¹_f(G_v, ad⁰ρ̄)` (classes of flat lifts):
`dim_κ L_v = dim_κ H⁰(G_v, ad⁰ρ̄) + [F_v : ℚ_ℓ]` — **the number consumed by T6.**
*Size M.* Deps: F5 (literature: FL-module rank count; DDT §2.4, CHT Lemma 2.4.1).
Sketch: tangent space = flat classes; count FL-module lifts of the residual filtered
module — a κ-dimension count of Hom spaces, `[F_v:ℚ_ℓ]` from the filtration choices per
embedding, `3` from framing minus scalars (4 − 1).

**F7. The tame condition at `v ∈ S` (companion, for T6's inputs).** The
`narrowTraceConditionFunctor`/`traceConditionFunctor` conditions
(`LiftFunctor.lean:131-149`, `map` fields already **proved**) define local deformation
rings at `v ∈ S`; prove the balanced count `dim_κ L_v = dim_κ H⁰(G_v, ad⁰ρ̄)` for the
associated Selmer condition.
*Size M.* Deps: none beyond the existing functors (literature: DDT §2.6 / Taylor–Wiles
"special" conditions `(literature-verify)`). Sketch: the rank-1-tame-quotient locus;
standard local Galois cohomology of `ad⁰` at `v ∤ ℓ` via local Euler characteristic 0.

## Part T — A7: instantiating the patching engine
*(Contract = the `variable` block of `REqualsT.lean:24-81`: Λ; family `R i`; modules
`M i` with `Free (Λ/Ann)`, `UniformlyBoundedRank`, `IsPatchingSystem`
(`Patching/Module.lean:533`); ultrafilter `F`; `𝔫`, `sR`, `sM`, `HCompat`; `R∞` domain
with `H₀`, `H : depth Λ Λ = ringKrullDim R∞`; `RtoT`, `hRtoT`.)*

**T1. TW element (group theory).** ρ̄|_{G_{F(ζ_ℓ)}} absolutely irreducible, ℓ ≥ 5:
for every `n` there is `σ ∈ G_{F(ζ_{ℓⁿ})}` with `ρ̄(σ)` having distinct κ-rational
eigenvalues. [Feeds on PR #1089's "irred + hardly ramified ⇒ abs irred over ℚ(ζ_ℓ)" —
watch, don't duplicate. The ℓ = 3 `F(√−3)` glitch is excluded by `hl : 3 < l`,
`Representable.lean:57-59`.]
*Size M.* Deps: L1 (literature: DDT Lemma 2.48 / Taylor–Wiles 1995 Lemma 1.2
`(literature-verify)`). Sketch: classification of subgroups of `GL₂(𝔽_ℓ)`; abs irred
over `F(ζ_ℓ)` rules out the exceptional/dihedral escapes for ℓ ≥ 5.

**T2. Cohomology vanishing.** `H¹(Gal(F(ζ_ℓ, ρ̄)/F), ad⁰ρ̄(1)) = 0` under the same
hypotheses (the inflation-restriction input making T4 work).
*Size M.* Deps: none (literature: DDT Lemma 2.48; FLT `ContCohomology` layer from the
PT freeze is the Lean substrate). Sketch: order of the group prime to ℓ except for a
controlled `SL₂(𝔽_ℓ)`-part whose `H¹` vanishes for ℓ ≥ 5.

**T3. Chebotarev consumption wrapper** [**shared-dependency node**]. Statement-only:
for `σ` as in T1 (or any conjugacy class of `Gal(L/F)`, `L/F` finite), infinitely many
`v` with `Frob_v = [σ]`; specialized: `Nv ≡ 1 (mod ℓⁿ)` and `ρ̄(Frob_v)` regular
semisimple. Discharge mode: `knownin1980s` (Chebotarev 1926 — era-eligible;
`FLT/Assumptions/KnownIn1980s.lean:79`). **Chebotarev exists NOWHERE in Lean** — CFT
adjudication repair 2 minted the absent node; also load-bearing for MB (D7), CBC
(S7/S8), and P5/G4 above. One wrapper, all consumers route through it.
*Size S.* Deps: none. Sketch: axiom-shaped statement pinning; no proof this campaign.

**T4. Cocycle-killing primes.** For each `0 ≠ ψ ∈ H¹_{L_Q^⊥}(ad⁰ρ̄(1))` there is a TW
prime `v` (T1+T3 shape) with `res_v ψ ≠ 0`.
*Size M.* Deps: T1, T2, T3 (literature: DDT Lemma 2.49 proof body). Sketch:
inflation-restriction (T2) reduces to nonvanishing of `ψ` on `G_{F(ζ_{ℓⁿ},ρ̄)}`; pick
`σ` in T1's class with `ψ(σ)` in the right eigenspace; Chebotarev realizes it as
`Frob_v`.

**T5. The sets `Q_n`.** For every `n ≥ 1` there is `Q_n` of TW primes, `#Q_n = q`,
`Nv ≡ 1 (mod ℓⁿ)`, `ρ̄(Frob_v)` distinct eigenvalues, and
`H¹_{L_{Q_n}^⊥}(ad⁰ρ̄(1)) = 0`.
*Size M.* Deps: T4, T6 (for the count staying `q`). Sketch: kill a basis one class at a
time; T6's formula shows each added prime drops dual-Selmer dimension by exactly one.

**T6. Wiles product formula instance — the PT-axiom spend point**
[**PT tag**]. `dim H¹_{L_Q} − dim H¹_{L_Q^⊥} = Σ_v (dim L_v − dim H⁰(G_v, ad⁰ρ̄))
− dim H⁰(G_F, ad⁰ρ̄) + …` evaluated with: F6 at `v|ℓ` (contributes `[F_v:ℚ_ℓ]`), F7 at
`v ∈ S` (contributes 0), T8's tame line at `v ∈ Q` (contributes 1 each), T7 at `v|∞`
(contributes −1 each); conclusion `dim H¹_{L_{Q_n}} = q` once dual Selmer dies (T5).
Consumes the **FROZEN PT order-formula axiom** (NSW 8.7.9 / DDT Thm 2.18 form,
`pt-adjudication.md`) — per `ret-adjudication.md` ruling 1 the axiom is spent HERE, via
A5+A6, **not** at `REqualsT.lean:76`. Carries PT's R1 caveat: its node 12 (global Euler
characteristic) is under-audited — inherit, do not re-derive. Boundary note: upstream
PR #1042 targets exactly this lemma (Gee Prop. 3.24) — announce before starting.
*Size M.* Deps: T5-interlocked, T7, F6, F7, T8, PT-axiom [FROZEN], A5 [absent —
tangent-space = H¹ identification, out of mandate, tagged]. Sketch: plug local numbers
into the order formula; convert orders to κ-dimensions.

**T7. Archimedean terms.** For `v | ∞` (F totally real, ρ̄ odd, ℓ > 2):
`dim H⁰(G_v, ad⁰ρ̄) = 1` and `H¹(G_v, ad⁰ρ̄) = 0` (order-2 group, ℓ odd).
*Size S.* Deps: none (Mathlib group cohomology of `ZMod 2`-actions; complex conjugation
via `NumberField.InfinitePlace`). Sketch: eigenvalue count of conj on `ad⁰` = (1,−1,−1).

**T8. Local structure at TW primes.** `v ∈ Q`, `Nv ≡ 1 (mod ℓ)`, `ρ̄(Frob_v)` distinct
eigenvalues: every lift `ρ|_{G_v}` splits `χ₁ ⊕ χ₂` with `χᵢ` tamely ramified
(Hensel/idempotent argument), giving (i) the tame character
`δ_v : Δ_v := ℓ-Sylow(k(v)ˣ) → R^×` — matching the `U₁` level shape
`(a *; 0 d) mod v, p ∤ ord(a/d)` (`Concrete.lean:874-876`) and the `U_v`-eigenvalue
needed by G6; (ii) `R_Q` is an `𝓞[Δ_Q]`-algebra (`Δ_Q = ∏_{v∈Q} Δ_v`) with
`R_Q / 𝔞_{Δ_Q} ≅ R_∅` (augmentation).
*Size M.* Deps: F-independent; uses L1-style Hensel splitting (literature: DDT
Lemma 2.44 `(literature-verify)`). Sketch: lift the two Frobenius eigenvalues by
Hensel; inertia acts through the tame quotient on each line; universal-property
bookkeeping for (ii).

**T9. Generator bound and `R∞ ↠ R_{Q_n}`.** `R_{Q_n}` is topologically generated over
𝓞 by `dim H¹_{L_{Q_n}} = q` elements [**consumes A5** — tangent space = Selmer group +
presentation bound; A5 is absent and out of mandate: tagged, this node is only the
instantiation]; choose (noncanonically) continuous surjections
`fRₒₒ n : R∞ := 𝓞⟦x₁,…,x_q⟧ →ₐ[Λ] R_{Q_n}` — the `fRₒₒ, hfRₒₒ, hfRₒₒ'` fields of the
contract.
*Size M.* Deps: T6, A5 [absent], T10. Sketch: complete local + tangent generation ⇒
power-series surjection; continuity from adic topologies.

**T10a. Power-series numerics (Mathlib-generic, upstreamable).**
`ringKrullDim 𝓞⟦x₁,…,x_q⟧ = q + 1 + dim` bookkeeping over the DVR-quotient of 𝓞, and
`Module.depth Λ Λ = q + 1` for `Λ := 𝓞⟦y₁,…,y_q⟧` via the regular sequence
`(ℓ, y₁, …, y_q)` — discharging `H₀ : ringKrullDim R∞ < ⊤` and
`H : depth Λ Λ = ringKrullDim R∞` (`REqualsT.lean:76`). **Mathlib gap flagged**: no
`PowerSeries` Krull-dimension file exists (mathlib-web; `KrullDimension.Polynomial`
only); `Module.depth` here is FLT-local (`FLT/Patching/Utils/Depth.lean:40`), not
Mathlib's `RingTheory.Regular.Depth`. Prove by hand: Noetherian local, dim = ht 𝔪 via
system of parameters; Mathlib has `WeierstrassPreparation` to help.
*Size M.* Deps: none. Sketch: induct on `q`: `𝓞⟦x⟧/(x) ≅ 𝓞` with `x` regular gives
both depth and dimension steps; `depth ≤ dim` is already in
`Utils/Depth.lean:161`.

**T10b. Instance bundle for Λ, R_i, R∞.** Discharge the typeclass rows of the contract:
`CompactSpace`, `IsAdicTopology`, `IsTopologicalRing` for `Λ, R_{Q_n}, R∞`;
`Algebra.TopologicallyFG ℤ R∞` (`Patching/Utils/TopologicallyFG.lean`); `IsDomain R∞`
(power series over domain); `IsLocalHom (algebraMap Λ R∞)`;
`Algebra.UniformlyBoundedRank R` (cardinality of `R_i/𝔪^k` bounded via the common
presentation `R∞ ↠ R_i` from T9).
*Size S.* Deps: T9, T10a. Sketch: instance plumbing against existing
`Patching/Utils/*` API; the rank bound is the one place T9's uniformity matters.

**T11a. Level-`Q` control isomorphism** [**D-9 tag**]. With
`M_Q := ((U₁ 𝒮_Q).toStruct.form D 𝓞)_{𝔪_Q}` (forms at level `U₁(S, Q)` localized at
the pullback of `𝔪`): a `T`-equivariant isomorphism `M_Q / 𝔞_{Δ_Q} M_Q ≅ M₀`
(`M₀` = level `U₁(S, ∅)` forms at `𝔪`), after choosing for each `v ∈ Q` the
`U_v`-eigenvalue lifting one Frobenius eigenvalue (T8). This node is where CBC's D-9
("Q = ∅ hardcode acceptable IF patching-side sufficiency proven by whoever pins")
is either discharged or dies — the sufficiency proof IS this isomorphism.
*Size M.* Deps: T8, G1 (per-level), `Concrete.lean` `U₁`/forms API [DONE]. Sketch:
definite case: forms are functions on a finite double-coset set; degeneracy maps are
explicit; distinct Frobenius eigenvalues make the `U_v`-projector an isomorphism at 𝔪
(no Ihara needed in the definite weight-2 setting).

**T11b. Freeness over `𝓞[Δ_Q]`** *(genuinely-hard flag — the arithmetic heart of TW)*.
`M_{Q_n}` is finite free over `𝓞[Δ_{Q_n}]` (equivalently over `Λ/Ann`, discharging
`Module.Free (Λ ⧸ Ann) (M i)`).
*Size M (hard).* Deps: T11a (literature: Taylor–Wiles 1995 §2; Diamond, "The Taylor–
Wiles construction and multiplicity one" (Invent. 128, 1997) for the module-theoretic
form `(literature-verify)`). Sketch: definite case: `M_Q` = 𝓞-valued functions on a
finite set on which `Δ_Q` acts; freeness ⟺ the action on the localized double-coset
space is free ⟺ stabilizers are ℓ-torsion-free at non-Eisenstein 𝔪 — a finite-group
computation on quaternionic class sets, hard because the stabilizer analysis is where
even-degree/discriminant-1 hypotheses actually bite.

**T11c. Patching-system instances.** `Nontrivial (M i)` (T11a + `M₀ ≠ 0` from the G2
witness), `Module.UniformlyBoundedRank Λ M` (rank `= rank_𝓞 M₀`, constant by T11a/b),
`IsPatchingSystem Λ M F` (`Patching/Module.lean:533`: `Ann M_i ≤ α` for `F`-many `i` —
from `Ann M_{Q_n} ⊆ (𝔫-adic terms)` shrinking as `Nv ≡ 1 mod ℓⁿ` deepens), for `F` any
nonprincipal ultrafilter on ℕ.
*Size S.* Deps: T11a, T11b. Sketch: instance discharge; the `∀ᶠ` is monotone in `n`.

**T12. Final assembly and the modularity transfer.** Instantiate
`ker_RtoT_le_nilradical` with the T/G data (`R₀ = R_∅`, `T₀ = T_𝔪`-image in
`End(M₀)`, `RtoT = φ` from G6, `hRtoT` from G6's construction, `𝔫` = augmentation
ideal, `sR` from T8(ii), `sM` from T11a, `HCompat` by construction): conclude
`ker(R_∅ → T_𝔪) ⊆ nilradical`. Payoff without any reducedness node: an ℓ-adic point
`x : R_∅ → 𝒪_{Q̄_ℓ}` (the ρ of the lifting theorem A1) has domain target, kills the
nilradical, hence factors through `T_𝔪` — i.e. **ρ is automorphic**
(`IsAutomorphicOfLevel` witness recovered from the `T_𝔪 →ₐ 𝒪` eigensystem). T_𝔪
reducedness is NOT on the critical path.
*Size S.* Deps: everything above (direct: G6, T8, T9, T10a/b, T11a-c). Sketch: apply
the proved theorem; the factoring argument is three lines of commutative algebra.

---

## Cross-reference ledger (consumption tags)

| Tag | Nodes | Note |
|---|---|---|
| **G17** (greps-adjudication ruling 3) | L1–L4 *are* G17's work breakdown; G3 consumes | This file discharges G17's decomposition obligation; grade M–L confirmed as 2S+2M |
| **FROZEN PT order-formula axiom** | T6 (sole consumer) | Spent at A7 via A5+A6 per ret-adjudication ruling 1 — NOT at `REqualsT.lean:76`; inherits PT R1 (node-12 under-audit) caveat |
| **Chebotarev** (CFT-absent, shared) | T3 (wrapper); P5, G4, T4 via T3 | `knownin1980s`-eligible (1926); same absent node as CFT repair 2, MB D7, CBC S7/S8 |
| **D-9** (CBC Q = ∅ hardcode) | T11a (discharge point), G6 | "Patching-side sufficiency proven by whoever pins" = the T11a isomorphism |
| **G15/G3 attachment boundary** | P5 (consumes field-valued ρ_λ) | Interface = `IsAutomorphicOfLevel`; G3 non-vacuity obligation inherited at G2 |
| **A4** (de Smit–Lenstra, ready-now) | G6, F4 consume; F1 overlaps its sorry set | Coordinate: F1 = `LiftFunctor.lean:117` is inside the A4 ready-now claim |
| **A5** (structure of R^univ, absent, out of mandate) | T9, T6 | The one in-mandate blocker with no owner — flag to panel |
| **Upstream watch** | T6 ↔ PR #1042 (Gee 3.24); T1 ↔ PR #1089 | Announce-before-start per standing ruling |

## Dependency order (one valid schedule)

Wave 0 (no deps): **P1, L1, T2, T3, T7, T10a, F1, F7** →
P2, F2, G1, T1 → P3, P4, F3, G2, T4, T8 → F4, T5/T6 (interlocked pair), G4-ready →
P5, F5, T10b-pre → L2, F6, G3, T11a → L3, L4, T9, T11b → G5, T10b, T11c → G6 → T12.

**Deepest chain (8 nodes):** P1 → P2 → P3 → P5 → G3 → G5 → G6 → T12
(equivalently T1 → T3 → T4 → T5 → T6 → T9 → T12, length 7, joins at T12).

## Node count, hard nodes, provable-today

- **37 nodes: 13 S + 24 M.** Per block: **A2 = 15 (7 S + 8 M)** (P: 2S+3M, L: 2S+2M,
  G: 3S+3M) · **A6 = 7 (1 S + 6 M)** · **A7 = 15 (5 S + 10 M)** (T3, T7, T10b, T11c,
  T12 are the S nodes). No L, no XL — the three XL rows tile completely.
- **Genuinely-hard M nodes (4):** L2 (pseudo-rep lifting algebra), G5 (flatness of the
  glued `T_𝔪`-rep), F5 (FL formal smoothness), T11b (TW freeness — the arithmetic
  heart). These four are where the mathematics, not the plumbing, lives.
- **Provable today (wave 0, recommended order):**
  1. **P1+P2** (pseudo-rep definition + trace-of-rep) — zero deps, pure algebra,
     unlocks all of Parts P/L/G; nothing in Mathlib or FLT to collide with (verified).
  2. **T10a** (dim/depth of `𝓞⟦x₁,…,x_q⟧`) — Mathlib-generic, fills a verified Mathlib
     gap, and is the exact discharge of the proved engine's `REqualsT.lean:76`
     hypothesis — highest leverage per line.
  3. **L1** (regular element in `GL₂(𝔽_ℓ)`, ℓ ≥ 5) — self-contained finite group
     theory; also feeds T1.
  (F1 is wave-0 too but sits inside the A4 ready-now claim — take it with A4, not
  separately.)
