import HexagonCover.GapChains

/-! Every one of the nine genuine positive-gap patterns forces b0>1/2.
Only actual light owners and gap-free intervening edges propagate inequalities. -/
namespace HexagonCover.GapPatternChains
open Configuration NormalizedHeavy BoundaryGaps
noncomputable section

theorem b_prefix {config : Fin 7 → UnitTriangle} (h : Normalized config) (k : Fin 5)
    (beforeClear : ∀i : Fin 5,i < k → ¬gap h.cover i.castSucc) :
    b h.cover k.castSucc  ≤  b h.cover 0 := by
  have step (i : Fin 5) (hi : i ≤ k) (hip : 0 < i) :
      b h.cover i.castSucc  <  b h.cover (i.castSucc-1) := by
    have hl := NoGapChain.light h i
    let j : Fin 5 := ⟨i.val-1,by omega⟩
    have hj : j < k := by dsimp [j]; change i.val-1 < k.val; change i.val ≤ k.val at hi; change 0 < i.val at hip; omega
    have he : j.castSucc=i.castSucc-1 := by
      apply Fin.ext
      rw [Fin.val_sub_one_of_ne_zero (by
        intro hz
        have hv := congrArg Fin.val hz
        change i.val=0 at hv
        change 0 < i.val at hip
        omega)]
      rfl
    have hjoin := le_of_not_gt (beforeClear j hj)
    change 1  ≤  b h.cover j.castSucc+a h.cover (j.castSucc+1) at hjoin
    rw [he,sub_add_cancel] at hjoin
    linarith
  fin_cases k
  · exact le_rfl
  · exact (step 1 (by decide) (by decide)).le
  · exact (step 2 (by decide) (by decide)).le.trans (step 1 (by decide) (by decide)).le
  · exact (step 3 (by decide) (by decide)).le.trans
      ((step 2 (by decide) (by decide)).le.trans (step 1 (by decide) (by decide)).le)
  · exact (step 4 (by decide) (by decide)).le.trans
      ((step 3 (by decide) (by decide)).le.trans
        ((step 2 (by decide) (by decide)).le.trans (step 1 (by decide) (by decide)).le))

theorem singleton_b0 {config : Fin 7 → UnitTriangle} (h : Normalized config) (k : Fin 5)
    (pattern : ∀i,gap h.cover i ↔ i=k.castSucc) : (1:ℝ)/2  <  b h.cover 0 := by
  have hk := (pattern k.castSucc).mpr rfl
  have last : ∀i : Fin 5,k < i → ¬gap h.cover i.castSucc := by
    intro i hi hg
    have he := congrArg Fin.val ((pattern i.castSucc).mp hg)
    change i.val=k.val at he
    change k.val < i.val at hi
    omega
  have beforeClear : ∀i : Fin 5,i < k → ¬gap h.cover i.castSucc := by
    intro i hi hg
    have he := congrArg Fin.val ((pattern i.castSucc).mp hg)
    change i.val=k.val at he
    change i.val < k.val at hi
    omega
  have hshort := GapScale.last_gap_short_upper h k last
  have he : k.castSucc+1=k.succ := by fin_cases k <;> decide
  have hwidth := GapChains.gap_width h k.castSucc hk
  rw [he] at hwidth
  have hM := GapScale.gap_nine_tenths h ⟨_,hk⟩
  have hM1 := (structure_bounds h).2.2.2.2.1
  have hrad := GapChains.trace_sqrt_gt_two (t:=1-M h) (by linarith) (by linarith)
  have hheavy := GapChains.heavy_short h
  have hb : (1:ℝ)/2  <  b h.cover k.castSucc := by linarith
  exact hb.trans_le (b_prefix h k beforeClear)

theorem pair_b0 {config : Fin 7 → UnitTriangle} (h : Normalized config) (k : Fin 4)
    (pattern : ∀i,gap h.cover i ↔ i=k.castSucc.castSucc ∨ i=k.succ.castSucc) :
    (1:ℝ)/2  <  b h.cover 0 := by
  have hfirst := (pattern k.castSucc.castSucc).mpr (Or.inl rfl)
  have hsecond := (pattern k.succ.castSucc).mpr (Or.inr rfl)
  have last : ∀i : Fin 5,k.succ < i → ¬gap h.cover i.castSucc := by
    intro i hi hg
    rcases (pattern i.castSucc).mp hg with he | he
    all_goals
      have hv := congrArg Fin.val he
      simp only [Fin.val_castSucc,Fin.val_succ] at hv
      change k.val+1 < i.val at hi
      omega
  have beforeClear : ∀i : Fin 5,i < k.castSucc → ¬gap h.cover i.castSucc := by
    intro i hi hg
    rcases (pattern i.castSucc).mp hg with he | he
    all_goals
      have hv := congrArg Fin.val he
      simp only [Fin.val_castSucc,Fin.val_succ] at hv
      change i.val < k.val at hi
      omega
  have hshort := GapScale.last_gap_short_upper h k.succ last
  have hM := GapScale.gap_nine_tenths h ⟨_,hfirst⟩
  have hheavy := GapChains.heavy_short h
  have hm : k.succ.castSucc-1=k.castSucc.castSucc := by fin_cases k <;> decide
  have hp : k.succ.castSucc+1=k.succ.succ := by fin_cases k <;> decide
  have hb := GapChains.adjacent_before_half h.cover k.succ.castSucc
    (by simpa only [hm] using hfirst) hsecond (by rw [hp]; linarith)
  rw [hm] at hb
  exact hb.trans_le (b_prefix h k.castSucc beforeClear)

theorem all_patterns_b0 {config : Fin 7 → UnitTriangle} (h : Normalized config)
    (somegap : ∃i,gap h.cover i) : (1:ℝ)/2  <  b h.cover 0 := by
  obtain ⟨S,hS,pattern⟩ := GapScale.normalized_nine_patterns h somegap
  simp only [ninePatterns,List.mem_cons,List.not_mem_nil,or_false] at hS
  rcases hS with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  · apply singleton_b0 h 0; intro i; simpa using pattern i
  · apply singleton_b0 h 1; intro i; simpa using pattern i
  · apply singleton_b0 h 2; intro i; simpa using pattern i
  · apply singleton_b0 h 3; intro i; simpa using pattern i
  · apply pair_b0 h 0; intro i; simpa using pattern i
  · apply pair_b0 h 1; intro i; simpa using pattern i
  · apply pair_b0 h 2; intro i; simpa using pattern i
  · apply singleton_b0 h 4; intro i; simpa using pattern i
  · apply pair_b0 h 3; intro i; simpa using pattern i

end
end HexagonCover.GapPatternChains
