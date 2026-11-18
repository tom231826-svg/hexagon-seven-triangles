import HexagonCover.HighMCentral

/-! Source-exposed E4 T3 direction elimination. The source's trigonometric
arc argument is expressed directly in Cartesian unit-normal coordinates,
including the two angular boundary cases before they are excluded. -/
namespace HexagonCover.E4T3Scalar
noncomputable section
local notation "h₀" => NICertificate.halfRoot

theorem upper_direction {a a3 b c d : ℝ} (hc : 0<c) (ha1 : a<1)
    (ha3 : a/2<a3) (hlight : a3+b<1)
    (hPa : c/2+h₀*d*(1-a)≤c*b) : h₀*d<c/2 := by
  by_contra hn
  have hp := mul_nonneg (show 0≤h₀*d-c/2 by linarith) (show 0≤1-a by linarith)
  have hl := mul_lt_mul_of_pos_left hlight hc
  have hs := mul_lt_mul_of_pos_left ha3 hc
  nlinarith only [hp,hPa,hl,hs]

/-- The complete forbidden negative arc, including its upper endpoint.
Every selected active normal is considered before any uniqueness claim. -/
theorem negative_direction_impossible {a a3 b c d : ℝ}
    (hc : 0<c) (hu : c^2+d^2=1) (ha3 : a/2<a3) (hb : a<b)
    (hd : h₀*d≤-c/2)
    (hbudget : c*(b+1/2-3*a/4-a3/2)-h₀*d*(1-a/2+a3)≤h₀) : False := by
  let A : ℝ := b+1/2-3*a/4-a3/2
  let B : ℝ := 1-a/2+a3
  have hh := ExtremeTriangle.halfRoot_pos
  have hB : 1<B := by dsimp [B]; linarith
  have hd0 : d<0 := by
    by_contra hn
    have hp := mul_nonneg hh.le (le_of_not_gt hn)
    linarith
  have hp := mul_nonneg (show 0≤-h₀*d-c/2 by linarith)
    (show 0≤-h₀*d+c/2 by nlinarith [mul_neg_of_pos_of_neg hh hd0])
  have hhdsq : h₀^2*d^2=(3/4:ℝ)*d^2 := by rw [ExtremeTriangle.halfRoot_sq]
  have hcH : c≤h₀ := by nlinarith only [hp,hhdsq,hu,ExtremeTriangle.halfRoot_sq,hc,hh]
  let low : ℝ := min (h₀*B) (A*h₀+h₀*B/2)
  have hlow : h₀<low := by
    apply lt_min
    · have hm := mul_lt_mul_of_pos_left hB hh
      linarith
    · have hm := mul_pos hh (show 0<b-a by linarith)
      dsimp [A,B]
      nlinarith only [hm]
  have hchord := HighMCentral.circle_chord (l:=0) (u:=h₀) (yl:=1) (yu:=1/2)
    (x:=c) (y:=-d) (α:=A) (β:=h₀*B) (B:=low)
    hh hc.le hcH (by norm_num) (by norm_num) (by linarith)
    (mul_nonneg hh.le (by linarith)) (by norm_num)
    (by nlinarith [ExtremeTriangle.halfRoot_sq]) (by nlinarith only [hu])
    (by dsimp only [low]; convert min_le_left (h₀*B) (A*h₀+h₀*B/2) using 1 <;> ring)
    (by dsimp only [low]; convert min_le_right (h₀*B) (A*h₀+h₀*B/2) using 1 <;> ring)
  dsimp [A,B] at hchord
  nlinarith only [hbudget,hchord,hlow]

theorem positive_direction {a a3 c d : ℝ} (hc : 0<c) (ha : 0<a) (ha1 : a<4/25)
    (ha3 : a3<1/3)
    (hPa : c*(1/2-3*a/4)-h₀*d*(1-a/2)≤c*a3) : 0<d := by
  by_contra hn
  have hdn : d≤0 := le_of_not_gt hn
  have hp := mul_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonneg_of_nonpos
    ExtremeTriangle.halfRoot_pos.le hdn) (show 0≤1-a/2 by linarith)
  have hm := mul_pos hc (show 0<1/2-3*a/4-a3 by linarith)
  nlinarith only [hp,hm,hPa]

def delta (c d : ℝ) : ℝ := 1/2-h₀*d/c
def scale (c : ℝ) : ℝ := h₀/c

theorem delta_bounds {c d : ℝ} (hc : 0<c) (hd : 0<d) (hupper : h₀*d<c/2) :
    0<delta c d ∧ delta c d<1/2 := by
  have hu : h₀*d/c<1/2 := (div_lt_iff₀ hc).mpr (by nlinarith only [hupper])
  have hp := div_pos (mul_pos ExtremeTriangle.halfRoot_pos hd) hc
  unfold delta
  constructor <;> linarith

theorem scale_identity {c d : ℝ} (hc : 0<c) (hu : c^2+d^2=1) :
    (scale c)^2=1-delta c d+(delta c d)^2 := by
  unfold scale delta
  field_simp [ne_of_gt hc]
  ring_nf
  rw [ExtremeTriangle.halfRoot_sq]
  nlinarith only [hu]

theorem Pa_rows {a a3 b c d : ℝ} (hc : 0<c)
    (hP0 : c/2+h₀*d*(1-a)≤c*b)
    (hP1 : c*(1/2-3*a/4)-h₀*d*(1-a/2)≤c*a3) :
    1-a/2-(1-a)*delta c d≤b ∧
    -a/2+(1-a/2)*delta c d≤a3 := by
  have hdid : c*(h₀*d/c)=h₀*d := by field_simp [ne_of_gt hc]
  constructor
  · apply (mul_le_mul_iff_of_pos_left hc).mp
    unfold delta
    nlinarith only [hP0,hdid,congrArg (fun z : ℝ => z*a) hdid]
  · apply (mul_le_mul_iff_of_pos_left hc).mp
    unfold delta
    nlinarith only [hP1,hdid,congrArg (fun z : ℝ => z*a) hdid]

end
end HexagonCover.E4T3Scalar

#print axioms HexagonCover.E4T3Scalar.negative_direction_impossible
#print axioms HexagonCover.E4T3Scalar.Pa_rows
