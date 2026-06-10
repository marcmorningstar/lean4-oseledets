import Oseledets.Lyapunov.FiltrationAssembly
import Oseledets.Lyapunov.ForwardAngle

/-!
# `FiltrationAssemblyBridge` — final-assembly deliverables for `Oseledets.oseledets_filtration`

This scratch file collects three independent deliverables that, together with the parallel
spectral-upper-bound work, close `Oseledets.oseledets_filtration`:

1. `hgrowth_of_upper_lower` — the per-vector EXACT growth interface (`hgrowth`) from the
   per-vector upper bound (`limsup ≤ specList`) and lower bound (`specList ≤ liminf`), squeezed
   to a genuine `Tendsto` via `tendsto_inv_mul_log_norm_cocycle_apply`.

2. `oseledets_filtration_of_interfaces'` — the KEY RE-POINTING of the assembly from the
   everywhere-measurable slow filtration `Vslow` instead of the only-a.e.-measurable `Vflag`,
   transporting the a.e. structural interfaces along the a.e. identification `Vslow = Vflag`.

3. `hspec_of_ergodic` — the ergodic spectrum-constancy interface (`hspec`), reducing it to the
   a.e. constancy of the (T-invariant) per-point Lyapunov spectrum.
-/

open MeasureTheory Filter Topology
open scoped Matrix Matrix.Norms.L2Operator

namespace Oseledets

variable {X : Type*} [MeasurableSpace X] {d : ℕ}

/-! ## Deliverable 1 — `hgrowth` from the per-vector upper and lower bounds

The `hgrowth` interface of `oseledets_filtration_of_interfaces` asks, a.e., for a genuine limit
`(1/n) log‖A⁽ⁿ⁾ v‖ → specList A T x i` on each stratum `Vflag castSucc \ Vflag succ`.  The committed
analytic core supplies the two one-sided bounds:

* the per-vector LOWER bound `specList A T x i ≤ liminf …` (from `log_le_liminf_log_cocycle_apply`
  at threshold `c = e^{specList i}`, packaged here as the hypothesis `hlb`); and
* the spectral UPPER bound `limsup … ≤ specList A T x i` (from the parallel worker, packaged here
  as the hypothesis `hub`).

The squeeze `tendsto_inv_mul_log_norm_cocycle_apply` (committed in `Forward.lean`) turns the two
bounds into the limit, modulo the two `IsBoundedUnder` side-conditions; we take those as the
minimal a.e. hypothesis `hbdd`. -/

/-- **`hgrowth` from upper + lower bounds.**  Given, a.e., the per-stratum-vector upper bound
(`limsup ≤ specList`), lower bound (`specList ≤ liminf`), and the two `IsBoundedUnder`
side-conditions, the per-vector growth interface of `oseledets_filtration_of_interfaces` holds.

The conclusion is stated with `Matrix.toEuclideanCLM` (the form consumed by the assembly); the
hypotheses use `Matrix.toEuclideanLin`, and the two coincide
(`Matrix.coe_toEuclideanCLM_eq_toEuclideanLin`). -/
theorem hgrowth_of_upper_lower
    {μ : Measure X} {T : X → X} (A : X → Matrix (Fin d) (Fin d) ℝ)
    (hub : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        limsup (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop ≤ specList A T x i)
    (hlb : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        specList A T x i ≤ liminf (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖) atTop)
    (hbdd : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        (IsBoundedUnder (· ≤ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖)) ∧
        (IsBoundedUnder (· ≥ ·) atTop (fun n : ℕ => (n : ℝ)⁻¹ *
          Real.log ‖Matrix.toEuclideanLin (cocycle A T n x) v‖))) :
    ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
          atTop (𝓝 (specList A T x i)) := by
  filter_upwards [hub, hlb, hbdd] with x hubx hlbx hbddx i v hv hvnot
  -- Rewrite the conclusion from `toEuclideanCLM` to `toEuclideanLin`.
  have hcoe : ∀ n : ℕ, (Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v)
      = Matrix.toEuclideanLin (cocycle A T n x) v := by
    intro n
    rw [← Matrix.coe_toEuclideanCLM_eq_toEuclideanLin]; rfl
  simp_rw [hcoe]
  obtain ⟨hba, hbb⟩ := hbddx i v hv hvnot
  exact tendsto_inv_mul_log_norm_cocycle_apply T A x v (specList A T x i)
    (hubx i v hv hvnot) (hlbx i v hv hvnot) hba hbb

/-! ## The `hmeas`-independent structural core of the committed assembly

`oseledets_filtration_of_interfaces` bundles the a.e. structural block with the existential
(`V := Vassembled`) and the `hmeas` argument.  To re-point onto an everywhere-measurable witness
we need that a.e. block *separately*, without the `hmeas` argument.  `vassembled_structure_ae`
extracts exactly that block; its proof is the committed assembly's structural body (lines 93–176 of
`FiltrationAssembly.lean`), verbatim, dropping only the existential-introduction `refine`. -/
theorem vassembled_structure_ae
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    (A : X → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (lam0 : ℕ → ℝ)
    (hspec : ∀ᵐ x ∂μ, ∃ h : specCard A T x = numExp lam0 d,
      ∀ i : Fin (specCard A T x), specList A T x i = expEnum lam0 d (Fin.cast h i))
    (hgrowth : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
          atTop (𝓝 (specList A T x i))) :
    ∀ᵐ x ∂μ,
      Vassembled A T (numExp lam0 d) 0 x = ⊤ ∧
      Vassembled A T (numExp lam0 d) (Fin.last (numExp lam0 d)) x = ⊥ ∧
      (∀ i : Fin (numExp lam0 d), Vassembled A T (numExp lam0 d) i.succ x
        < Vassembled A T (numExp lam0 d) i.castSucc x) ∧
      (∀ i : Fin (numExp lam0 d + 1),
        Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap
          (Vassembled A T (numExp lam0 d) i x) = Vassembled A T (numExp lam0 d) i (T x)) ∧
      (∀ i : Fin (numExp lam0 d), ∀ v ∈ (Vassembled A T (numExp lam0 d) i.castSucc x :
          Set (EuclideanSpace ℝ (Fin d))),
          v ∉ Vassembled A T (numExp lam0 d) i.succ x →
          Tendsto
            (fun n : ℕ => (n : ℝ)⁻¹ *
              Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
            atTop (𝓝 (expEnum lam0 d i))) := by
  classical
  set k := numExp lam0 d with hk
  have hspec' := hT.toMeasurePreserving.quasiMeasurePreserving.ae hspec
  have hUM := isUltrametricGrowth_lambdaBar hT hA hAmeas hint hint'
  have hUM' := hT.toMeasurePreserving.quasiMeasurePreserving.ae hUM
  have hsubeq := Vflag_equivariant hT hA hAmeas hint hint'
  have hspeceq := spectrum_equivariant_ae hT hA hAmeas hint hint'
  filter_upwards [hspec, hspec', hUM, hUM', hsubeq, hspeceq, hgrowth]
    with x hsx hsTx hx hTx hmapeq hseq hgx
  obtain ⟨hcardx, hlistx⟩ := hsx
  obtain ⟨hcardTx, hlistTx⟩ := hsTx
  have hcardeq : specCard A T x = specCard A T (T x) := by
    rw [specCard, specCard, hseq]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [Vassembled_of_eq hcardx]
    have : (Fin.cast (by rw [hcardx] : k + 1 = specCard A T x + 1) (0 : Fin (k + 1)))
        = (0 : Fin (specCard A T x + 1)) := by
      apply Fin.ext; simp
    rw [this]; exact Vflag_zero hx
  · rw [Vassembled_of_eq hcardx]
    have : (Fin.cast (by rw [hcardx] : k + 1 = specCard A T x + 1) (Fin.last k))
        = Fin.last (specCard A T x) := by
      apply Fin.ext; simp [hcardx]
    rw [this]; exact Vflag_last A T x
  · intro i
    rw [Vassembled_of_eq hcardx, Vassembled_of_eq hcardx]
    set i' : Fin (specCard A T x) := Fin.cast hcardx.symm i with hi'
    have hsucc : (Fin.cast (by rw [hcardx] : k + 1 = specCard A T x + 1) i.succ)
        = i'.succ := by apply Fin.ext; simp [hi']
    have hcast : (Fin.cast (by rw [hcardx] : k + 1 = specCard A T x + 1) i.castSucc)
        = i'.castSucc := by apply Fin.ext; simp [hi']
    rw [hsucc, hcast]
    exact Vflag_strictAnti hx i'
  · intro i
    rw [Vassembled_of_eq hcardx, Vassembled_of_eq hcardTx]
    by_cases hint_i : (i : ℕ) < specCard A T x
    · have hcx : ((Fin.cast (by rw [hcardx] : k + 1 = specCard A T x + 1) i : Fin (specCard A T x + 1)) : ℕ)
          < specCard A T x := hint_i
      have hcTx : ((Fin.cast (by rw [hcardTx] : k + 1 = specCard A T (T x) + 1) i :
            Fin (specCard A T (T x) + 1)) : ℕ) < specCard A T (T x) := by
        simp only [Fin.val_cast]; omega
      rw [Vflag_of_lt hcx, Vflag_of_lt hcTx]
      have hjk : (i : ℕ) < numExp lam0 d := by rw [hcardx] at hint_i; exact hint_i
      set j : Fin (numExp lam0 d) := ⟨(i : ℕ), hjk⟩ with hj
      have hthrx : specList A T x ⟨_, hcx⟩ = expEnum lam0 d j := by
        rw [hlistx]
        exact congrArg (expEnum lam0 d) (Fin.ext (by simp [hj]))
      have hthrTx : specList A T (T x) ⟨_, hcTx⟩ = expEnum lam0 d j := by
        rw [hlistTx]
        exact congrArg (expEnum lam0 d) (Fin.ext (by simp [hj]))
      rw [hthrx, hthrTx]
      exact hmapeq (expEnum lam0 d j)
    · have hnx : ¬ ((Fin.cast (by rw [hcardx] : k + 1 = specCard A T x + 1) i :
          Fin (specCard A T x + 1)) : ℕ) < specCard A T x := hint_i
      have hnTx : ¬ ((Fin.cast (by rw [hcardTx] : k + 1 = specCard A T (T x) + 1) i :
          Fin (specCard A T (T x) + 1)) : ℕ) < specCard A T (T x) := by
        simp only [Fin.val_cast]; omega
      rw [Vflag, dif_neg hnx, Vflag, dif_neg hnTx, Submodule.map_bot]
  · intro i v hv hvnot
    rw [Vassembled_of_eq hcardx] at hv hvnot
    set i' : Fin (specCard A T x) := Fin.cast hcardx.symm i with hi'
    have hcast : (Fin.cast (by rw [hcardx] : k + 1 = specCard A T x + 1) i.castSucc)
        = i'.castSucc := by apply Fin.ext; simp [hi']
    have hsucc : (Fin.cast (by rw [hcardx] : k + 1 = specCard A T x + 1) i.succ)
        = i'.succ := by apply Fin.ext; simp [hi']
    rw [hcast] at hv
    rw [hsucc] at hvnot
    have hgrow := hgx i' v hv hvnot
    have hval : specList A T x i' = expEnum lam0 d i := by
      rw [hlistx i']
      have : Fin.cast hcardx i' = i := by apply Fin.ext; simp [hi']
      rw [this]
    rwa [hval] at hgrow

/-! ## Deliverable 2 — re-pointing the assembly onto an everywhere-measurable family

`Vassembled` is built from the limsup flag `Vflag`, whose measurability is only available a.e.
The `MeasurableSubspace` predicate is an *everywhere* statement, so `hmeas` cannot be discharged
for `Vassembled` directly.  The fix is to carry the structural conclusion on a *different*,
everywhere-measurable family `V'` (built from the slow spectral filtration `Vslow`, whose
measurability is the committed `measurableSubspace_Vslow`), and transport the a.e. structural
facts along the a.e. identification `V' = Vassembled`.

This `oseledets_filtration_of_interfaces'` takes:
* the SAME `hspec`/`hgrowth` interfaces as the committed assembly (they feed `Vassembled`);
* `hmeas'` — `MeasurableSubspace` for the slow-based family `V'` (discharged via
  `measurableSubspace_Vslow`); and
* `hae` — the a.e. identification `V' i x = Vassembled A T (numExp lam0 d) i x`.

It produces the verbatim `oseledets_filtration` target with witness `V := V'`.  The structural
a.e. block is the committed `Vassembled` block (obtained from `oseledets_filtration_of_interfaces`)
rewritten, level by level, through `hae`.

The a.e. identification `hae` is itself the L11 mathematical content (`Vslow = Vflag` a.e.); it is
NOT yet committed in the repo, so it is taken here as the minimal cleanly-typed hypothesis.  Once a
committed `Vslow = Vflag` lemma exists it discharges `hae` directly. -/
theorem oseledets_filtration_of_interfaces'
    {μ : Measure X} [IsProbabilityMeasure μ] {T : X → X}
    (hT : Ergodic T μ)
    (A : X → Matrix (Fin d) (Fin d) ℝ)
    (hA : ∀ x, (A x).det ≠ 0)
    (hAmeas : Measurable A)
    (hint : IntegrableLogNorm A μ)
    (hint' : IntegrableLogNorm (fun x => (A x)⁻¹) μ)
    (lam0 : ℕ → ℝ)
    (hspec : ∀ᵐ x ∂μ, ∃ h : specCard A T x = numExp lam0 d,
      ∀ i : Fin (specCard A T x), specList A T x i = expEnum lam0 d (Fin.cast h i))
    (V' : Fin (numExp lam0 d + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d)))
    (hmeas' : ∀ i, MeasurableSubspace (fun x => V' i x))
    (hae : ∀ᵐ x ∂μ, ∀ i, V' i x = Vassembled A T (numExp lam0 d) i x)
    (hgrowth : ∀ᵐ x ∂μ, ∀ i : Fin (specCard A T x),
      ∀ v ∈ (Vflag A T x i.castSucc : Set (EuclideanSpace ℝ (Fin d))),
        v ∉ Vflag A T x i.succ →
        Tendsto
          (fun n : ℕ => (n : ℝ)⁻¹ *
            Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
          atTop (𝓝 (specList A T x i))) :
    ∃ (k : ℕ) (lam : Fin k → ℝ)
      (V : Fin (k + 1) → X → Submodule ℝ (EuclideanSpace ℝ (Fin d))),
      StrictAnti lam ∧
      (∀ i, MeasurableSubspace fun x => V i x) ∧
      ∀ᵐ x ∂μ,
        V 0 x = ⊤ ∧ V (Fin.last k) x = ⊥ ∧
        (∀ i : Fin k, V i.succ x < V i.castSucc x) ∧
        (∀ i : Fin (k + 1),
          Submodule.map (Matrix.toEuclideanCLM (𝕜 := ℝ) (A x)).toLinearMap (V i x) = V i (T x)) ∧
        (∀ i : Fin k, ∀ v ∈ (V i.castSucc x : Set (EuclideanSpace ℝ (Fin d))),
            v ∉ V i.succ x →
            Tendsto
              (fun n : ℕ => (n : ℝ)⁻¹ *
                Real.log ‖Matrix.toEuclideanCLM (𝕜 := ℝ) (cocycle A T n x) v‖)
              atTop (𝓝 (lam i))) := by
  classical
  refine ⟨numExp lam0 d, expEnum lam0 d, V', expEnum_strictAnti lam0 d, hmeas', ?_⟩
  -- Structural a.e. block on `Vassembled` (the `hmeas`-independent core of the committed assembly),
  -- then transport level-by-level through `hae`.
  have hstruct := vassembled_structure_ae hT A hA hAmeas hint hint' lam0 hspec hgrowth
  -- The identification transported to the image point `T x` (needed for the equivariance level).
  have haeT := hT.toMeasurePreserving.quasiMeasurePreserving.ae hae
  filter_upwards [hstruct, hae, haeT] with x hsx haex haeTx
  obtain ⟨h0, hlast, hstrict, hmap, hgrow⟩ := hsx
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [haex 0]; exact h0
  · rw [haex (Fin.last (numExp lam0 d))]; exact hlast
  · intro i; rw [haex i.succ, haex i.castSucc]; exact hstrict i
  · intro i; rw [haex i, haeTx i]; exact hmap i
  · intro i v hv hvnot
    rw [haex i.castSucc] at hv
    rw [haex i.succ] at hvnot
    exact hgrow i v hv hvnot

/-! ## Deliverable 3 — the `hspec` ergodic spectrum-constancy interface

`hspec` asks that, a.e., the per-point limsup spectrum (`specCard`/`specList`, built from the finite
limsup spectrum `spectrum A T x` of `lambdaBar`) coincides with the deterministic
singular-value spectrum (`numExp`/`expEnum`, built from `distinctExp lam0 d`).

The committed `spectrum_equivariant_ae` provides the T-invariance `spectrum A T x = spectrum A T (T x)`
a.e.; ergodicity upgrades this to a.e. *constancy* of the finite set `spectrum A T x`, and the
deep `Λ`-spectral identification pins that constant set to `distinctExp lam0 d`.  Packaging both as
the single hypothesis `hspecconst : ∀ᵐ x, spectrum A T x = distinctExp lam0 d`, the `hspec` shape is
then a pure `Finset`/`Fin`-reindexing computation: `specCard` and `numExp` are both the cardinality
of the (now-equal) finite set, and `specList` and `expEnum` are both its descending
`orderEmbOfFin`-enumeration, so they agree along the cardinality cast.

The constancy-to-`distinctExp` step (`hspecconst`) is the L11/ergodic content that is not yet
committed in the repo; it is taken here as the minimal cleanly-typed hypothesis. -/

/-- **`hspec` from a.e. spectrum constancy.**  If the per-point limsup spectrum `spectrum A T x`
equals the deterministic distinct-exponent set `distinctExp lam0 d` a.e., then the `hspec` interface
of `oseledets_filtration_of_interfaces` holds: a.e. the spectrum cardinality equals `numExp lam0 d`
and the descending enumeration `specList` equals `expEnum lam0 d` along the cardinality cast. -/
theorem hspec_of_spectrum_const
    {μ : Measure X} {T : X → X} (A : X → Matrix (Fin d) (Fin d) ℝ) (lam0 : ℕ → ℝ)
    (hspecconst : ∀ᵐ x ∂μ, spectrum A T x = distinctExp lam0 d) :
    ∀ᵐ x ∂μ, ∃ h : specCard A T x = numExp lam0 d,
      ∀ i : Fin (specCard A T x), specList A T x i = expEnum lam0 d (Fin.cast h i) := by
  filter_upwards [hspecconst] with x hx
  -- The cardinality cast.
  have hcard : specCard A T x = numExp lam0 d := by
    rw [specCard, numExp, hx]
  refine ⟨hcard, fun i => ?_⟩
  -- Both enumerations are the descending `orderEmbOfFin` of the *same* finite set; on equal
  -- finsets the embedding values agree iff the index values agree
  -- (`Finset.orderEmbOfFin_eq_orderEmbOfFin_iff`).
  have key : ∀ (s t : Finset ℝ), s = t → ∀ {p q : ℕ} (hs : s.card = p) (ht : t.card = q)
      (a : Fin p) (b : Fin q), (a : ℕ) = (b : ℕ) →
      s.orderEmbOfFin hs a = t.orderEmbOfFin ht b := by
    rintro s t rfl p q hs ht a b hab
    rw [Finset.orderEmbOfFin_eq_orderEmbOfFin_iff]; exact hab
  rw [specList, expEnum]
  exact key _ _ hx rfl rfl i.rev (Fin.cast hcard i).rev (by simp [Fin.val_rev, hcard])

/-! ## Axiom audit -/

#print axioms hgrowth_of_upper_lower
#print axioms vassembled_structure_ae
#print axioms oseledets_filtration_of_interfaces'
#print axioms hspec_of_spectrum_const

end Oseledets
