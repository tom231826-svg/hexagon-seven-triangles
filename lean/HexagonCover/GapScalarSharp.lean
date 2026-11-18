import HexagonCover.IntruderReach
import HexagonCover.CentralDisk

/-! Exact scalar gap obstruction on t∈[2/25,1/10]. This follows the frozen
b3-gap-sharpen.md comparison; it is source-exposed, not an independent blind derivation. -/
namespace HexagonCover.GapScalarSharp
open CommonReach
noncomputable section

theorem strict_comparison {t x : ℝ} (ht : (2:ℝ)/25 ≤ t) (ht' : t ≤ (1:ℝ)/10)
    (hx0 : 0 ≤ x) (hxhalf : x ≤ (1:ℝ)/2)
    (hpoly : x^2+(1-t)*x+(1-t)^2 ≤ 1) :
    x*(1-x) < 2*Real.sqrt 3*rho t-4*(rho t)^2 := by
  let z := t*(1-t)
  let p := rho t
  have ht0 : 0 < t := by linarith
  have ht1 : t < 1 := by linarith
  have hz : 0 < z := mul_pos ht0 (by linarith)
  have hzbound : z ≤ (9:ℝ)/100 := by
    dsimp [z]
    nlinarith only [mul_nonneg (show 0 ≤ 1/10-t by linarith) (show 0 ≤ 9/10-t by linarith)]
  have hp0 : 0 < p := (CentralDisk.rho_bounds ht0 ht1).1
  have hsqrt := Real.sq_sqrt (radiusSq_pos t).le
  have hsqrt0 := Real.sqrt_nonneg (radiusSq t)
  have hpidentity : z=p*(2-p) := by
    dsimp [z,p,rho,radiusSq] at *
    nlinarith only [hsqrt]
  have hpupper : p < (461:ℝ)/10000 := by
    have hr : (91:ℝ)/100 ≤ radiusSq t := by dsimp [radiusSq]; dsimp [z] at hzbound; linarith only [hzbound]
    have hs : (9539:ℝ)/10000 < Real.sqrt (radiusSq t) := by nlinarith only [hsqrt,hsqrt0,hr]
    dsimp [p,rho]
    linarith only [hs]
  have hs3 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 3)
  have hs30 := Real.sqrt_nonneg (3:ℝ)
  have hs3low : (433:ℝ)/250 < Real.sqrt 3 := by nlinarith only [hs3,hs30]
  have hratio : (32796:ℝ)/19539*(2-p) < 2*Real.sqrt 3-4*p := by linarith only [hs3low,hpupper]
  have hG : (32796:ℝ)/19539*z < 2*Real.sqrt 3*p-4*p^2 := by
    have hm := mul_lt_mul_of_pos_right hratio hp0
    nlinarith only [hm,hpidentity]
  let S := Real.sqrt (1+6*t-3*t^2)
  let F := (S-1+t)/2
  have hrad : 0 ≤ 1+6*t-3*t^2 := by
    nlinarith only [ht0,mul_nonneg ht0.le (show 0 ≤ 1/10-t by linarith)]
  have hS : S^2=1+6*t-3*t^2 := Real.sq_sqrt hrad
  have hS0 : 0 ≤ S := Real.sqrt_nonneg _
  have hSlo : (6043:ℝ)/5000 < S := by
    have hradlo : (913:ℝ)/625 ≤ 1+6*t-3*t^2 := by
      nlinarith only [mul_nonneg (show 0 ≤ t-2/25 by linarith) (show 0 ≤ 48/25-t by linarith)]
    nlinarith only [hradlo,hS,hS0]
  have hShi : S < 2-t := by nlinarith only [hS,hS0,ht',sq_nonneg t]
  have hF0 : 0 < F := by dsimp [F]; linarith only [hSlo,ht0]
  have hFhalf : F < (1:ℝ)/2 := by dsimp [F]; linarith only [hShi]
  have hFpoly : F^2+(1-t)*F+(1-t)^2=1 := by dsimp [F]; nlinarith only [hS]
  have hxF : x ≤ F := by
    by_contra hn
    have hf : F < x := lt_of_not_ge hn
    have hsq : F^2 < x^2 := (sq_lt_sq₀ hF0.le hx0).mpr hf
    have hm := mul_lt_mul_of_pos_left hf (show 0 < 1-t by linarith)
    linarith only [hpoly,hFpoly,hsq,hm]
  have hxproduct : x*(1-x) ≤ F*(1-F) := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hxF) (show 0 ≤ 1-F-x by linarith)]
  have hidentity : F*(1-F)*(S+1+t)=2*z*(2-t) := by
    dsimp [F,z]
    nlinarith only [hS, congrArg (fun y : ℝ => S*y) hS,
      congrArg (fun y : ℝ => t*y) hS]
  have hFprod : 0 < F*(1-F) := mul_pos hF0 (by linarith)
  have hden : (11443:ℝ)/5000 < S+1+t := by linarith only [hSlo,ht]
  have hnum : 2*(2-t) ≤ (96:ℝ)/25 := by linarith only [ht]
  have hupper : F*(1-F) < (19200:ℝ)/11443*z := by
    have hd := mul_lt_mul_of_pos_left hden hFprod
    have hn := mul_le_mul_of_nonneg_left hnum hz.le
    nlinarith only [hd,hn,hidentity]
  have hcoeff : (19200:ℝ)/11443*z < (32796:ℝ)/19539*z := by
    exact mul_lt_mul_of_pos_right (by norm_num) hz
  change x*(1-x) < 2*Real.sqrt 3*p-4*p^2
  exact hxproduct.trans_lt (hupper.trans (hcoeff.trans hG))

end
end HexagonCover.GapScalarSharp
