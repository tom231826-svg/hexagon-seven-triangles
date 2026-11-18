import HexagonCover.CornerTransport

/-! Actual reach lengths are equivariant under a single rigid motion of the
whole configuration. Strict anchor disks are transported with the same pieces. -/
namespace HexagonCover.ReachEquiv
open HexagonCover.Configuration QSymmetry Symmetry CornerTransport Normalization
noncomputable section

theorem lineMap_apply (f : Plane ≃ᵃⁱ[ℝ] Plane) (u v : Plane) (t : ℝ) :
    f (AffineMap.lineMap u v t)=AffineMap.lineMap (f u) (f v) t :=
  f.toAffineIsometry.toAffineMap.apply_lineMap u v t

def mapReach (f : Plane ≃ᵃⁱ[ℝ] Plane) {T : UnitTriangle} {u v : Plane}
    (R : EdgeReach.Reach T u v) : EdgeReach.Reach (mapTriangle f T) (f u) (f v) where
  length := R.length
  positive := R.positive
  lt_one := R.lt_one
  endpoint := by
    rw [←lineMap_apply, map_region]
    exact ⟨AffineMap.lineMap u v R.length,R.endpoint,rfl⟩
  character t ht := by
    rw [←lineMap_apply,map_region]
    constructor
    · rintro ⟨p,hp,he⟩
      have hp' : p=AffineMap.lineMap u v t := f.injective he
      rw [hp'] at hp
      exact (R.character t ht).mp hp
    · intro hle
      exact ⟨AffineMap.lineMap u v t,(R.character t ht).mpr hle,rfl⟩

theorem map_length (f : Plane ≃ᵃⁱ[ℝ] Plane) {T U : UnitTriangle} {u v x y : Plane}
    (R : EdgeReach.Reach T u v) (S : EdgeReach.Reach U x y)
    (hT : mapTriangle f T=U) (hu : f u=x) (hv : f v=y) : R.length=S.length := by
  subst U
  subst x
  subst y
  exact EdgeReach.length_unique (mapReach f R) S

theorem strictCover (action : Action) {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) : StrictCover (action.transform config) where
  covered := action.covered h.covered
  anchorBalls i := by
    obtain ⟨r,hr,hball⟩ := h.anchorBalls (action.roles.symm i)
    have hb := action_ball action (config (action.roles.symm i))
      (qAnchor 1 (action.roles.symm i)) hball
    rw [action.anchors,Equiv.apply_symm_apply] at hb
    exact ⟨r,hr,hb⟩

theorem triangle_at (action : Action) (config : Fin 7 → UnitTriangle)
    (i j : Fin 7) (hij : action.roles i=j) :
    mapTriangle action.motion (config i)=action.transform config j := by
  rw [←hij,Action.transform,Equiv.symm_apply_apply]

theorem vertex_at (action : Action) (i j : Fin 6)
    (hij : action.roles i.castSucc=j.castSucc) :
    action.motion (hexVertex 1 i)=hexVertex 1 j := by
  have he := action.anchors i.castSucc
  rw [qAnchor_outer,hij,qAnchor_outer] at he
  exact he

theorem right_right (action : Action) {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i j : Fin 6)
    (h0 : action.roles i.castSucc=j.castSucc)
    (h1 : action.roles (i+1).castSucc=(j+1).castSucc) :
    b h i=b (strictCover action h) j :=
  map_length action.motion (rightReach h i) (rightReach (strictCover action h) j)
    (triangle_at action config _ _ h0) (vertex_at action i j h0)
    (vertex_at action (i+1) (j+1) h1)

theorem left_left (action : Action) {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i j : Fin 6)
    (h0 : action.roles i.castSucc=j.castSucc)
    (h1 : action.roles (i-1).castSucc=(j-1).castSucc) :
    a h i=a (strictCover action h) j :=
  map_length action.motion (leftReach h i) (leftReach (strictCover action h) j)
    (triangle_at action config _ _ h0) (vertex_at action i j h0)
    (vertex_at action (i-1) (j-1) h1)

theorem right_left (action : Action) {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i j : Fin 6)
    (h0 : action.roles i.castSucc=j.castSucc)
    (h1 : action.roles (i+1).castSucc=(j-1).castSucc) :
    b h i=a (strictCover action h) j :=
  map_length action.motion (rightReach h i) (leftReach (strictCover action h) j)
    (triangle_at action config _ _ h0) (vertex_at action i j h0)
    (vertex_at action (i+1) (j-1) h1)

theorem left_right (action : Action) {config : Fin 7 → UnitTriangle}
    (h : StrictCover config) (i j : Fin 6)
    (h0 : action.roles i.castSucc=j.castSucc)
    (h1 : action.roles (i-1).castSucc=(j+1).castSucc) :
    a h i=b (strictCover action h) j :=
  map_length action.motion (leftReach h i) (rightReach (strictCover action h) j)
    (triangle_at action config _ _ h0) (vertex_at action i j h0)
    (vertex_at action (i-1) (j+1) h1)

end
end HexagonCover.ReachEquiv
