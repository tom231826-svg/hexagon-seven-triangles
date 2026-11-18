import Mathlib

/-! Finite support-event analysis. This module starts the completeness proof:
a positive trigonometric linear branch cannot have a local minimum, and a
positive local minimum of a finite support envelope must be a switching event.
Enumeration/binding of the original convex-hull events is a separate obligation. -/
namespace HexagonCover.SupportEvents
open Filter
open scoped Topology
noncomputable section

def trigLinear (A B θ : ℝ) : ℝ := A * Real.cos θ + B * Real.sin θ

theorem trigLinear_not_localMin (A B θ : ℝ) (hpos : 0 < trigLinear A B θ) :
    ¬ IsLocalMin (trigLinear A B) θ := by
  intro hmin
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff.mp hmin
  let ε : ℝ := min (δ / 2) (Real.pi / 2)
  have hε : 0 < ε := lt_min (by linarith) (by positivity)
  have hεδ : ε < δ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hεπ : ε ≤ Real.pi := (min_le_right _ _).trans (by linarith [Real.pi_pos])
  have hplus : trigLinear A B θ ≤ trigLinear A B (θ + ε) := by
    apply hball
    rw [Real.dist_eq]
    simpa [abs_of_pos hε] using hεδ
  have hminus : trigLinear A B θ ≤ trigLinear A B (θ - ε) := by
    apply hball
    rw [Real.dist_eq]
    simpa [abs_of_pos hε, abs_of_neg (neg_neg_of_pos hε)] using hεδ
  have hcos : Real.cos ε < 1 := by
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (by norm_num : (0 : ℝ) ≤ 0) hεπ hε
  have hadd : trigLinear A B (θ + ε) + trigLinear A B (θ - ε) =
      2 * Real.cos ε * trigLinear A B θ := by
    simp only [trigLinear, Real.cos_add, Real.cos_sub, Real.sin_add, Real.sin_sub]
    ring
  nlinarith [mul_pos (sub_pos.mpr hcos) hpos]

def envelope {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ → ℝ) (θ : ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (fun i => f i θ)

theorem le_envelope {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ → ℝ) (i : ι) (θ : ℝ) : f i θ ≤ envelope f θ :=
  Finset.le_sup' (fun j => f j θ) (Finset.mem_univ i)

theorem envelope_eq_of_dominates {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ → ℝ) (i : ι) (θ : ℝ) (h : ∀ j, f j θ ≤ f i θ) :
    envelope f θ = f i θ := by
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun j _ => h j)
  · exact le_envelope f i θ

theorem envelope_locally_eq_of_unique {ι : Type*} [Fintype ι] [Nonempty ι]
    (f : ι → ℝ → ℝ) (hc : ∀ j, Continuous (f j)) (i : ι) (θ : ℝ)
    (hu : ∀ j, j ≠ i → f j θ < f i θ) :
    envelope f =ᶠ[𝓝 θ] f i := by
  have hd : ∀ᶠ x in 𝓝 θ, ∀ j, f j x ≤ f i x := by
    rw [Filter.eventually_all]
    intro j
    by_cases hj : j = i
    · subst j
      exact Filter.Eventually.of_forall (fun x => le_rfl)
    · filter_upwards [(hc j).continuousAt.eventually_lt (hc i).continuousAt (hu j hj)] with x hx
      exact hx.le
  filter_upwards [hd] with x hx
  exact envelope_eq_of_dominates f i x hx

theorem trig_envelope_min_has_tie {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : ι → ℝ) (θ : ℝ)
    (hmin : IsLocalMin (envelope (fun i => trigLinear (A i) (B i))) θ)
    (hpos : 0 < envelope (fun i => trigLinear (A i) (B i)) θ) :
    ∃ i j, i ≠ j ∧
      trigLinear (A i) (B i) θ = envelope (fun i => trigLinear (A i) (B i)) θ ∧
      trigLinear (A j) (B j) θ = envelope (fun i => trigLinear (A i) (B i)) θ := by
  classical
  let f : ι → ℝ → ℝ := fun i => trigLinear (A i) (B i)
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty (fun i => f i θ)
  change envelope f θ = f i θ at hi
  by_contra hno
  have hu : ∀ j, j ≠ i → f j θ < f i θ := by
    intro j hji
    have hle : f j θ ≤ f i θ := (le_envelope f j θ).trans_eq hi
    apply lt_of_le_of_ne hle
    intro heq
    exact hno ⟨i, j, Ne.symm hji, hi.symm, heq.trans hi.symm⟩
  have hc : ∀ j, Continuous (f j) := by
    intro j
    exact (continuous_const.mul Real.continuous_cos).add
      (continuous_const.mul Real.continuous_sin)
  have hlocal := hmin.congr (envelope_locally_eq_of_unique f hc i θ hu)
  have hp : 0 < f i θ := by
    rw [← hi]
    exact hpos
  exact trigLinear_not_localMin (A i) (B i) θ hp hlocal


theorem trig_envelope_continuous {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : ι → ℝ) : Continuous (envelope (fun i => trigLinear (A i) (B i))) := by
  apply Continuous.finset_sup'_apply Finset.univ_nonempty
  intro i _
  exact (continuous_const.mul Real.continuous_cos).add
    (continuous_const.mul Real.continuous_sin)

theorem trig_envelope_periodic {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : ι → ℝ) :
    Function.Periodic (envelope (fun i => trigLinear (A i) (B i))) (2 * Real.pi) := by
  intro θ
  simp only [envelope, trigLinear, Real.cos_add_two_pi, Real.sin_add_two_pi]

/-- A positive finite support envelope attains its global minimum at a tie.
The later geometric binding must identify these ties with the recorded edge events. -/
theorem trig_envelope_minimum_at_tie {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : ι → ℝ)
    (hpos : ∀ θ, 0 < envelope (fun i => trigLinear (A i) (B i)) θ) :
    ∃ θ i j, i ≠ j ∧
      trigLinear (A i) (B i) θ = envelope (fun i => trigLinear (A i) (B i)) θ ∧
      trigLinear (A j) (B j) θ = envelope (fun i => trigLinear (A i) (B i)) θ ∧
      ∀ φ, envelope (fun i => trigLinear (A i) (B i)) θ ≤
        envelope (fun i => trigLinear (A i) (B i)) φ := by
  have hc := (trig_envelope_periodic A B).compact_of_continuous
    (by positivity : 2 * Real.pi ≠ 0) (trig_envelope_continuous A B)
  obtain ⟨_, ⟨θ, rfl⟩, hleast⟩ := hc.exists_isLeast (Set.range_nonempty _)
  have hglobal : ∀ φ, envelope (fun i => trigLinear (A i) (B i)) θ ≤
      envelope (fun i => trigLinear (A i) (B i)) φ := by
    intro φ
    exact hleast (Set.mem_range_self φ)
  have hlocal : IsLocalMin (envelope (fun i => trigLinear (A i) (B i))) θ :=
    Filter.Eventually.of_forall hglobal
  obtain ⟨i, j, hij, hi, hj⟩ := trig_envelope_min_has_tie A B θ hlocal (hpos θ)
  exact ⟨θ, i, j, hij, hi, hj, hglobal⟩

/-- Checking every tied active branch is sufficient for a strict uniform bound.
This is a mathematical completeness result, not yet the original hull parser. -/
theorem bound_of_all_ties {ι : Type*} [Fintype ι] [Nonempty ι]
    (A B : ι → ℝ) (bound : ℝ)
    (hpos : ∀ θ, 0 < envelope (fun i => trigLinear (A i) (B i)) θ)
    (hevent : ∀ θ i j, i ≠ j →
      trigLinear (A i) (B i) θ = envelope (fun i => trigLinear (A i) (B i)) θ →
      trigLinear (A j) (B j) θ = envelope (fun i => trigLinear (A i) (B i)) θ →
      bound < envelope (fun i => trigLinear (A i) (B i)) θ) :
    ∀ θ, bound < envelope (fun i => trigLinear (A i) (B i)) θ := by
  obtain ⟨φ, i, j, hij, hi, hj, hmin⟩ := trig_envelope_minimum_at_tie A B hpos
  intro θ
  exact (hevent φ i j hij hi hj).trans_le (hmin θ)

end
end HexagonCover.SupportEvents
